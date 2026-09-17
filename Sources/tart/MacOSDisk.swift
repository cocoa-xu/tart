import Foundation
import zlib

struct MacOSDisk {
  static func resize(_ diskURL: URL, to size: UInt64, stagingURL: URL) throws {
    let source = try FileHandle(forReadingFrom: diskURL)
    defer { try? source.close() }
    let currentSize = try source.seekToEnd()
    guard size >= currentSize else {
      throw RuntimeError.InvalidDiskSize("new disk size must not be smaller than the current disk size")
    }

    var table = try PartitionTable(source, diskSize: currentSize)
    guard size.isMultiple(of: table.blockSize) else {
      throw RuntimeError.InvalidDiskSize("new disk size must align to the disk block size")
    }
    let lastBlock = size / table.blockSize - 1
    let lastUsableBlock = lastBlock - table.tableBlocks - 1
    let recoveryBlocks = table.recoveryEnd - table.recoveryStart + 1
    let recoveryStart = lastUsableBlock - recoveryBlocks + 1
    guard recoveryStart >= table.recoveryStart else {
      throw RuntimeError.InvalidDiskSize("new disk size leaves insufficient space for Recovery")
    }
    if size == currentSize && recoveryStart == table.recoveryStart {
      return
    }

    try FileManager.default.copyItem(at: diskURL, to: stagingURL)
    defer { try? FileManager.default.removeItem(at: stagingURL) }
    let destination = try FileHandle(forUpdating: stagingURL)
    defer { try? destination.close() }
    try destination.truncate(atOffset: size)

    try source.seek(toOffset: table.recoveryStart * table.blockSize)
    try destination.seek(toOffset: recoveryStart * table.blockSize)
    var remaining = recoveryBlocks * table.blockSize
    while remaining > 0 {
      try Task.checkCancellation()
      let count = Int(min(remaining, 8 * 1024 * 1024))
      let data = try source.readExactly(count)
      try destination.write(contentsOf: data)
      remaining -= UInt64(count)
    }

    table.entries.setUInt64(recoveryStart, at: 2 * 128 + 32)
    table.entries.setUInt64(lastUsableBlock, at: 2 * 128 + 40)
    let checksum = table.entries.crc32Checksum
    table.primary.setUInt64(lastBlock, at: 32)
    table.primary.setUInt64(lastUsableBlock, at: 48)
    table.primary.setUInt32(checksum, at: 88)
    table.primary.updateHeaderChecksum()
    table.backup.setUInt64(lastBlock, at: 24)
    table.backup.setUInt64(lastUsableBlock, at: 48)
    table.backup.setUInt64(lastBlock - table.tableBlocks, at: 72)
    table.backup.setUInt32(checksum, at: 88)
    table.backup.updateHeaderChecksum()
    table.mbr.setUInt32(UInt32(min(lastBlock, UInt64(UInt32.max))), at: 446 + 12)

    try destination.write(table.entries, at: (lastBlock - table.tableBlocks) * table.blockSize)
    try destination.write(table.backup, at: lastBlock * table.blockSize)
    try destination.write(table.entries, at: 2 * table.blockSize)
    try destination.write(table.primary, at: table.blockSize)
    try destination.write(table.mbr, at: 0)
    try destination.synchronize()
    try destination.close()

    let staged = try FileHandle(forReadingFrom: stagingURL)
    defer { try? staged.close() }
    _ = try PartitionTable(staged, diskSize: size)
    try Task.checkCancellation()
    if rename(stagingURL.path, diskURL.path) != 0 {
      throw POSIXError(POSIXErrorCode(rawValue: errno) ?? .EIO)
    }
  }

  private struct PartitionTable {
    let blockSize: UInt64
    let tableBlocks: UInt64
    var mbr: Data
    var primary: Data
    var backup: Data
    var entries: Data
    let recoveryStart: UInt64
    let recoveryEnd: UInt64

    init(_ file: FileHandle, diskSize: UInt64) throws {
      let signature = Data("EFI PART".utf8)
      try file.seek(toOffset: 512)
      if try file.readExactly(8) == signature {
        blockSize = 512
      } else {
        try file.seek(toOffset: 4096)
        guard try file.readExactly(8) == signature else {
          throw RuntimeError.FailedToResizeDisk("disk does not contain a supported GPT")
        }
        blockSize = 4096
      }
      guard diskSize.isMultiple(of: blockSize), diskSize / blockSize >= 68 else {
        throw RuntimeError.FailedToResizeDisk("invalid GPT disk size")
      }
      tableBlocks = 128 * 128 / blockSize
      mbr = try file.readExactly(Int(blockSize), at: 0)
      primary = try file.readExactly(Int(blockSize), at: blockSize)
      try Self.validateHeader(primary)
      let backupBlock = primary.uint64(at: 32)
      let firstUsableBlock = primary.uint64(at: 40)
      let lastUsableBlock = primary.uint64(at: 48)
      guard primary.uint64(at: 24) == 1,
            primary.uint64(at: 72) == 2,
            backupBlock >= 2 * tableBlocks + 3,
            backupBlock < diskSize / blockSize,
            firstUsableBlock >= 2 + tableBlocks,
            lastUsableBlock < backupBlock - tableBlocks,
            firstUsableBlock <= lastUsableBlock else {
        throw RuntimeError.FailedToResizeDisk("invalid primary GPT bounds")
      }
      backup = try file.readExactly(Int(blockSize), at: backupBlock * blockSize)
      try Self.validateHeader(backup)
      guard backup.uint64(at: 24) == backupBlock,
            backup.uint64(at: 32) == 1,
            backup.uint64(at: 72) == backupBlock - tableBlocks,
            backup[40..<72] == primary[40..<72],
            backup[80..<92] == primary[80..<92] else {
        throw RuntimeError.FailedToResizeDisk("primary and backup GPT headers do not match")
      }
      entries = try file.readExactly(128 * 128, at: 2 * blockSize)
      let backupEntries = try file.readExactly(128 * 128, at: (backupBlock - tableBlocks) * blockSize)
      guard entries == backupEntries, entries.crc32Checksum == primary.uint32(at: 88) else {
        throw RuntimeError.FailedToResizeDisk("invalid GPT partition checksum or backup")
      }

      let partitionTypes: [[UInt8]] = [
        [0x61, 0x69, 0x64, 0x69, 0x00, 0x67, 0xAA, 0x11, 0xAA, 0x11, 0x00, 0x30, 0x65, 0x43, 0xEC, 0xAC],
        [0xEF, 0x57, 0x34, 0x7C, 0x00, 0x00, 0xAA, 0x11, 0xAA, 0x11, 0x00, 0x30, 0x65, 0x43, 0xEC, 0xAC],
        [0x72, 0x76, 0x63, 0x52, 0x00, 0x79, 0xAA, 0x11, 0xAA, 0x11, 0x00, 0x30, 0x65, 0x43, 0xEC, 0xAC],
      ]
      var previousEnd = firstUsableBlock - 1
      for (index, type) in partitionTypes.enumerated() {
        let offset = index * 128
        let start = entries.uint64(at: offset + 32)
        let end = entries.uint64(at: offset + 40)
        guard entries[offset..<offset + 16] == Data(type),
              start > previousEnd, end >= start, end <= lastUsableBlock else {
          throw RuntimeError.FailedToResizeDisk("expected iBoot, APFS and Recovery partitions in disk order")
        }
        previousEnd = end
      }
      for index in 3..<128 {
        guard entries[index * 128..<index * 128 + 16].allSatisfy({ $0 == 0 }) else {
          throw RuntimeError.FailedToResizeDisk("disk contains additional partitions")
        }
      }
      guard mbr[510] == 0x55, mbr[511] == 0xAA,
            mbr[446 + 4] == 0xEE, mbr.uint32(at: 446 + 8) == 1,
            mbr[462..<510].allSatisfy({ $0 == 0 }) else {
        throw RuntimeError.FailedToResizeDisk("invalid protective MBR")
      }
      recoveryStart = entries.uint64(at: 2 * 128 + 32)
      recoveryEnd = entries.uint64(at: 2 * 128 + 40)
    }

    private static func validateHeader(_ header: Data) throws {
      guard header.prefix(8) == Data("EFI PART".utf8),
            header.uint32(at: 8) == 0x00010000,
            header.uint32(at: 12) == 92,
            header.uint32(at: 20) == 0,
            header.uint32(at: 80) == 128,
            header.uint32(at: 84) == 128 else {
        throw RuntimeError.FailedToResizeDisk("unsupported GPT header")
      }
      var bytes = header.prefix(92)
      bytes.setUInt32(0, at: 16)
      guard bytes.crc32Checksum == header.uint32(at: 16) else {
        throw RuntimeError.FailedToResizeDisk("invalid GPT header checksum")
      }
    }
  }
}

private extension FileHandle {
  func readExactly(_ count: Int, at offset: UInt64? = nil) throws -> Data {
    if let offset {
      try seek(toOffset: offset)
    }
    guard let data = try read(upToCount: count), data.count == count else {
      throw RuntimeError.FailedToResizeDisk("unexpected end of disk image")
    }
    return data
  }

  func write(_ data: Data, at offset: UInt64) throws {
    try seek(toOffset: offset)
    try write(contentsOf: data)
  }
}

private extension Data {
  func uint32(at offset: Int) -> UInt32 {
    withUnsafeBytes { UInt32(littleEndian: $0.loadUnaligned(fromByteOffset: offset, as: UInt32.self)) }
  }

  func uint64(at offset: Int) -> UInt64 {
    withUnsafeBytes { UInt64(littleEndian: $0.loadUnaligned(fromByteOffset: offset, as: UInt64.self)) }
  }

  mutating func setUInt32(_ value: UInt32, at offset: Int) {
    Swift.withUnsafeBytes(of: value.littleEndian) { replaceSubrange(offset..<offset + 4, with: $0) }
  }

  mutating func setUInt64(_ value: UInt64, at offset: Int) {
    Swift.withUnsafeBytes(of: value.littleEndian) { replaceSubrange(offset..<offset + 8, with: $0) }
  }

  var crc32Checksum: UInt32 {
    withUnsafeBytes { UInt32(crc32(0, $0.bindMemory(to: UInt8.self).baseAddress, UInt32(count))) }
  }

  mutating func updateHeaderChecksum() {
    setUInt32(0, at: 16)
    setUInt32(prefix(92).crc32Checksum, at: 16)
  }
}
