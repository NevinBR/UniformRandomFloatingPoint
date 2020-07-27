// Author: Nevin Brackett-Rozinsky
//
// This is a proof-of-concept implementation to generate random floating-point
// numbers, with probability proportional to the distance between each
// representable value and the next. In other words, the behavior is as if
// choosing a real number in the range, and rounding down to the next
// representible value. For closed ranges, we extend it into a half-open range
// bounded by upperBound.nextUp
//
// Note on terminology: this file uses "binade" pervasively to refer to the
// set of all floating-point values with the same sign and raw exponent. When
// the word "binade" appears below, it has that meaning. The implementation
// cares about values with the same raw exponent, and the word "binade" is
// repurposed for that definition here.

extension BinaryFloatingPoint where RawSignificand: FixedWidthInteger {
  // MARK: Range
  
  // Generate a random floating-point value in a range.
  public static func uniformRandom(in range: Range<Self>) -> Self {
    var generator = SystemRandomNumberGenerator()
    return uniformRandom(in: range, using: &generator)
  }
  
  
  // Generate a random floating-point value in a range, using a specified
  // random number generator.
  public static func uniformRandom<R: RandomNumberGenerator>(in range: Range<Self>, using generator: inout R) -> Self {
    precondition(range.upperBound.isFinite)
    return uniformRandomRoundedDown(in: range, using: &generator)
  }
  
  
  // MARK: ClosedRange
  
  // Generate a random floating-point value in a closed range.
  public static func uniformRandom(in range: ClosedRange<Self>) -> Self {
    var generator = SystemRandomNumberGenerator()
    return uniformRandom(in: range, using: &generator)
  }
  
  
  // Generate a random floating-point value in a closed range, using a specified
  // random number generator.
  public static func uniformRandom<R: RandomNumberGenerator>(in range: ClosedRange<Self>, using generator: inout R) -> Self {
    precondition(range.upperBound.isFinite)
    let extendedRange = range.lowerBound ..< range.upperBound.nextUp
    return uniformRandomRoundedDown(in: extendedRange, using: &generator)
  }
  
  
  // MARK: Implementation
  
  // Our goal is to produce a result equivalent to choosing a real number
  // uniformly at random within the given range then rounding down to the
  // nearest representable floating-point value.
  //
  // The general strategy is to expand the range so its bounds are equal and
  // opposite powers of 2. Split that new range into 2^60 equal sections*, and
  // note that each section either fits in a single raw binade, or it has 0 as
  // one bound and a power of 2 as the other.
  //
  // Find which sections the bounds of the original range land in, and choose
  // a section at random which overlaps the original range. Finally, pick a
  // representable value at random from that section. If it is in the original
  // range we are done, otherwise try again.
  //
  // To reduce the probability of landing outside the original range, we handle
  // very small ranges separately, where the span can be counted in terms of
  // the smallest ulp in the range without overflowing.
  //
  // * We use only 2^60 sections rather than 2^64 for optimization reasons as
  //   described in the comment for `sectionScale` at the end of the file.
  static func uniformRandomRoundedDown<R: RandomNumberGenerator>(in range: Range<Self>, using generator: inout R) -> Self {
    precondition(!range.isEmpty)
    precondition(range.lowerBound.isFinite)
    // If range.upperBound == .infinity, treat it as if it were one ulp above
    // .greatestFiniteMagnitude
    
    
    // Fast path
    //
    // Simple ranges bounded by the start of a raw binade and either 0 or the
    // negative of the first bound. We expect these ranges will be the most
    // common in practice, as they include 0..<1 and -1..<1.
    
    let (a, b) = (range.lowerBound, range.upperBound)
    
    if (a.significandBitPattern == 0) && (b.significandBitPattern == 0) {
      let (aExp, bExp) = (a.exponentBitPattern, b.exponentBitPattern)
      
      if aExp == 0 {
        return randomUpToExponent(bExp, using: &generator)
      } else if a == -b {
        return randomUpToExponent(bExp, allowNegative: true, using: &generator)
      } else if bExp == 0 {
        return -randomUpToExponent(aExp, using: &generator).nextUp
      }
    }
    
    
    // Small range
    //
    // Ranges that cross up to one raw binade boundary are handled here to
    // ensure the `while true` loop in the general case usually succeeds.
    //
    // This only needs to be done when it is possible for more than one
    // representable number in the second-largest raw binade of the range to
    // fall in the same section.
    
    if significandBitCount > Int64.bitWidth &- sectionScale &- 3  {
      if let x = smallRangeUniformRandom(in: range, using: &generator) {
        return x
      }
    }
    
    
    // General case
    //
    // Take a range centered at 0 with bounds having raw significand 0, which
    // contains the target range, and divide it into 2^60 equal sections. Find
    // which section the bounds of the original range land in, and choose a
    // section at random between them (inclusive).
    //
    // Pick a random number uniformly within that section. If it is within the
    // original range return it, otherwise repeat.
    
    let (sections, e) = sectionsAndExponent(range)
    
    while true {
      let n = Int64.random(in: sections, using: &generator)
      let x = uniformRandomInSection(n, maxExponent: e, using: &generator)
      if range.contains(x) { return x }
    }
  }
  
  
  // MARK: General case
  
  // Every raw binade (except raw exponent 0) spans a width equal to that of
  // all raw binades below it (starting at 0).
  //
  // Similarly, the set of integers with the leading 1 in a given position
  // spans a width equal to that of all smaller integers (starting from 0).
  //
  // This correspondence between raw exponents of floating-point numbers on the
  // one hand, and binary logarithms of integers on the other hand, forms the
  // basis for our strategy.
  //
  // The following diagram illustrates both ideas:
  //
  // ________________                |                ________________
  //                 ________        |        ________
  //                         ____    |    ____
  //                             __  |  __
  //                               _ | _
  //                                _|_
  //                                 |
  //                                 0
  //
  // In order to choose a representable number in a given range, we first
  // extend the range to have bounds at the start of a raw binade, mirrored
  // about 0, then divide it into 2^60 sections. Note that half (or 2^59) of
  // those sections are non-negative.
  //
  // This lines up raw binades of the extended range with binary logarithms of
  // 59-bit integers. The number of leading zeros in the integer matches the
  // difference between the raw exponent of the binade, and the maximum raw
  // exponent in the extended range.
  //
  // The integers represent sections, each of which spans 1 / 2^60 of the
  // extended range. Section zero, which is bounded below by 0, may span
  // multiple raw binades. However, each positive section fits within a single
  // raw binade. Negative sections are essentially mirrored.
  //
  // The following diagram shows an example of a range and its extension:
  //
  // ________________                |                ________________
  //                 ________        |        ________     |
  //                    |    ____    |    ____             |
  //                    |        __  |  __                 |
  //                    |          _ | _                   |
  //                    |           _|_                    |
  //                    |            |                     |
  //                    a____________0_____________________b
  //
  // By finding the sections that the bounds of the range fall in, we are able
  // to choose a section between then simply by producing a random integer.
  // Then we can choose a random floating-point value within that section.
  //
  // Most of the time this will land within the original range and we are done.
  // In the rare case that we selected one of the sections at the ends of the
  // range, and the value chosen within that section landed outside the range,
  // we simply try again.
  
  
  // Convert a range of Self into a range of Int64 section numbers and the
  // corresponding maximum exponent.
  @inline(__always)
  static func sectionsAndExponent(_ range: Range<Self>) -> (sections: ClosedRange<Int64>, maxExponent: RawExponent) {
    let (a, b) = (range.lowerBound, range.upperBound)
    
    let m = maximumMagnitude(a, b)
    var e = m.exponentBitPattern
    if m.significandBitPattern != 0 { e += 1 }
    
    let (low, _) = a.sectionNumber(maxExponent: e)
    let (h, isLowerBound) = b.sectionNumber(maxExponent: e)
    let high = isLowerBound ? h &- 1 : h
    return (low...high, e)
  }
  
  
  // Take the range with bounds having raw exponent equal to maxExponent and
  // 0 significand, and split it into 2^60 sections. Find which section self
  // falls in.
  //
  // The section number for a non-negative value is equal to its significand
  // (including implicit bit), shifted so there are (eMax - e + sectionScale)
  // zeros before the implicit bit. Negative numbers have their section offset
  // by 1, except at the boundary between sections.
  func sectionNumber(maxExponent eMax: RawExponent) -> (section: Int64, isLowerBound: Bool) {
    let (e, s) = (exponentBitPattern, significandBitPattern)
    
    precondition(eMax > 0)
    precondition(e <= eMax, "Exponent exceeds maximum")
    
    if self == 0 { return (section: 0, isLowerBound: true) }
    
    var n: UInt64
    let isLowerBound: Bool
    
    let w = UInt64.bitWidth &- Self.sectionScale &- 1
    let z = eMax - max(1, e)   // Number of leading zeros before implicit bit
    
    if z < w {
      // We will need (w - z) significand bits.
      let bitsNeeded = w &- Int(truncatingIfNeeded: z)
      let shift = bitsNeeded &- Self.significandBitCount
      
      if shift < 0 {
        // It is okay to use `&>>` here because `-shift` is less than
        // `Self.significandBitCount`. We know this because (z < w) implies
        // (bitsNeeded >= 1), so (shift >= 1 - Self.significandBitCount).
        let usableBits = s &>> -shift
        isLowerBound = s == (usableBits &<< -shift)
        n = UInt64(truncatingIfNeeded: usableBits)
        
      } else {
        // It is okay to use `&<<` here because `shift` is less than
        // `UInt64.bitWidth`. We know this because:
        // shift <= bitsNeeded < w < UInt64.bitWidth
        n = UInt64(truncatingIfNeeded: s) &<< shift
        isLowerBound = true
      }
      
      if e != 0 {
        // As above, `&<<` is okay because (bitsNeeded < UInt64.bitWidth).
        n |= (1 &<< bitsNeeded)
      }
    } else if (z == w) && (e != 0) {
      (n, isLowerBound) = (1, s == 0)
    } else {
      (n, isLowerBound) = (0, false)
    }
    
    if self < 0 {
      n = isLowerBound ? (0 &- n) : ~n
    }
    return (Int64(bitPattern: n), isLowerBound)
  }
  
  
  // Get a random number in a single section.
  //
  // The number of leading zeros (minus the section scale) gives the number of
  // binades below maxExponent. The raw exponent is found by subtraction, but
  // not less than zero.
  //
  // The remaining bits form the implicit bit and the significand. If there
  // are not enough bits to fill the significand, that indicates the section
  // contains multiple representable values. In which case, the low bits are
  // chosen uniformly at random.
  //
  // Section 0 may span multiple raw binades, and is handled specially.
  //
  // Negative sections are nearly mirrors of the positive, but off by one.
  static func uniformRandomInSection<R: RandomNumberGenerator>(_ section: Int64, maxExponent eMax: RawExponent, using generator: inout R) -> Self {
    let k = (section < 0) ? ~section : section
    let n = UInt64(bitPattern: k)
    let w = UInt64.bitWidth &- sectionScale
    let x: Self
    
    if (n == 0) && (eMax >= w) {
      // Section 0 spanning at least one full raw binade
      let e = eMax - RawExponent(truncatingIfNeeded: w &- 1)
      x = randomUpToExponent(e, using: &generator)
    } else {
      // Each other section fits in a single raw binade
      let z = n.leadingZeroBitCount &- sectionScale
      precondition(z >= 0)
      
      let isNormal = z < eMax
      let e = isNormal ? eMax - RawExponent(truncatingIfNeeded: z) : 0
      let unusedBitCount = isNormal ? z &+ 1 : Int(truncatingIfNeeded: eMax)
      let availableBitCount = w &- unusedBitCount
      let shift = significandBitCount &- availableBitCount
      
      var s: RawSignificand
      
      if shift <= 0 {
        s = RawSignificand(truncatingIfNeeded: n >> -shift)
      } else {
        s = generator.next()
        s &= (1 << shift) &- 1
        s |= RawSignificand(truncatingIfNeeded: n) << shift
      }
      
      s &= significandMask
      x = Self(sign: .plus, exponentBitPattern: e, significandBitPattern: s)
    }
    
    return (section < 0) ? -x.nextUp : x
  }
  
  
  // MARK: Fast path
  
  // Choose a random non-negative representable number with raw exponent less
  // than eMax, with probability proportional to its ulp.
  //
  // If allowNegative is true, then with 50% probability negate the next-higher
  // representable value and return that instead.
  @inline(__always)
  static func randomUpToExponent<R: RandomNumberGenerator>(_ eMax: RawExponent, allowNegative: Bool = false, using generator: inout R) -> Self {
    if eMax == 0 { return 0 }
    
    let e: RawExponent
    var bits: UInt64
    var bitCount: Int
    
    if (exponentBitCount < Int.bitWidth) || (eMax <= Int.max) {
      // eMax fits in an Int, so use the specialized version
      var eInt = Int(truncatingIfNeeded: eMax)
      (eInt, bits, bitCount) = randomExponent(upperBound: eInt, using: &generator)
      e = RawExponent(truncatingIfNeeded: eInt)
    } else {
      (e, bits, bitCount) = randomExponent(upperBound: eMax, using: &generator)
    }
    
    var s: RawSignificand
    
    if bitCount < significandBitCount {
      s = generator.next()
      
      if bitCount == 0 {
        bits = UInt64(truncatingIfNeeded: s >> significandBitCount)
        bitCount = RawSignificand.bitWidth &- significandBitCount
      }
    } else {
      s = RawSignificand(truncatingIfNeeded: bits)
      bits >>= significandBitCount
      bitCount &-= significandBitCount
    }
    
    var isNegative = false
    
    if allowNegative {
      if bitCount == 0 {
        isNegative = Bool.random(using: &generator)
      } else {
        isNegative = (bits & 1) == 0
      }
    }
    
    s &= significandMask
    let x = Self(sign: .plus, exponentBitPattern: e, significandBitPattern: s)
    return isNegative ? -x.nextUp : x
  }
  
  
  // Choose a raw exponent at random less than upperBound, with probability
  // proportional to the width of the raw binade with that raw exponent. Also
  // return any additional random bits that were left over from this process,
  // and a count of how many.
  //
  // This function is generic over T because it is faster when specialized for
  // Int. The alternative was to have two copies, one for Int alone and the
  // other for RawExponent. Making it generic avoids that duplication.
  @inline(__always)
  static func randomExponent<R: RandomNumberGenerator, T: BinaryInteger>(upperBound: T, using generator: inout R) -> (e: T, bits: UInt64, bitCount: Int) {
    if upperBound <= 1 { return (0, 0, 0) }
    
    var e = upperBound - 1
    var bits: UInt64
    var z: Int
    
    // Each raw binade (except raw exponent 0) is the same width as all raw
    // binades below it. So with 50% probability we stop where we are, and with
    // 50% probability we reduce the exponent, until either we stop or reach 0.
    //
    // We use the high bits of a random number to represent these coin flips,
    // treating 1 as "stop" and 0 as "continue".
    repeat {
      bits = generator.next()
      z = bits.leadingZeroBitCount
      if e <= z {
        // Enough "continues" to reach raw exponent zero.
        // The rest of the bits are still random.
        return (0, bits, UInt64.bitWidth &- Int(truncatingIfNeeded: e))
      }
      e -= T(truncatingIfNeeded: z)
    } while bits == 0
    
    // All the bits after the first "stop" are still random.
    return (e, bits, UInt64.bitWidth &- 1 &- z)
  }
  
  
  // MARK: Small range
  
  // If the range spans 0 or 1 raw binades and its bounds are close enough
  // together, then the distance between them can be counted in terms of the
  // smallest ulp in the range.
  //
  // For types with spare bits in the significand, this could be done for
  // ranges that span a larger number of raw binades, but there is little
  // benefit to doing so.
  //
  // The purpose here is to ensure that the large range path is only taken
  // when there is a low probability of needing multiple attempts. Currently,
  // that probability is less than 1 in 2^56 in the worst case.
  static func smallRangeUniformRandom<R: RandomNumberGenerator>(in range: Range<Self>, using generator: inout R) -> Self? {
    let (a, b) = (range.lowerBound, range.upperBound)
    let aExp = a.exponentBitPattern
    let bExp = b.exponentBitPattern
    
    if a.sign == b.sign {
      let sign = a.sign
      let eSpan = (sign == .plus) ? (bExp - aExp) : (aExp - bExp)
      if eSpan > 1 { return nil }
      
      let aSig = a.significandBitPattern
      let bSig = b.significandBitPattern
      let (low, high) = (sign == .plus) ? (aSig, bSig) : (bSig, aSig)
      let x: Self
      
      if eSpan == 0 {
        // Single raw binade
        let s = RawSignificand.random(in: low..<high, using: &generator)
        x = Self(sign: sign, exponentBitPattern: aExp, significandBitPattern: s)
        
      } else {
        // Adjacent raw binades
        let eBase = (sign == .plus) ? aExp : bExp
        let isHigh: Bool
        let s: RawSignificand
        
        if (eBase == 0) && (high <= low) {
          // One subnormal
          let span = high &+ (significandMask &- low)
          let r = RawSignificand.random(in: 0...span, using: &generator)
          isHigh = r < high
          s = isHigh ? r : low &+ (r &- high)
          
        } else if high <= (low &>> 1) {
          // Both normal
          let h2 = high &<< 1
          let span = h2 &+ (significandMask &- low)
          let r = RawSignificand.random(in: 0...span, using: &generator)
          isHigh = r < h2
          s = isHigh ? (r &>> 1) : low &+ (r &- h2)
          
        } else {
          // Large range
          return nil
        }
        
        let e = isHigh ? eBase + 1 : eBase
        x = Self(sign: sign, exponentBitPattern: e, significandBitPattern: s)
      }
      
      return (sign == .plus) ? x : x.nextDown
      
    } else if (aExp == 0) && (bExp == 0) {
      // Subnormal opposite signs
      let bSig = b.significandBitPattern
      let span = a.significandBitPattern &+ bSig
      if span < bSig { return nil }
      
      let r = RawSignificand.random(in: 0 ..< span, using: &generator)
      let sign: FloatingPointSign = (r < bSig) ? .plus : .minus
      let s = (r < bSig) ? r : r &- bSig &+ 1
      return Self(sign: sign, exponentBitPattern: 0, significandBitPattern: s)
      
    } else {
      // Large range
      return nil
    }
  }
  
  
  // MARK: Helpers
  
  @inline(__always)
  static var significandMask: RawSignificand {
    // We use `<<` here because it is possible that a floating-point type
    // could have (significandBitCount == RawSignificand.bitwidth).
    return (1 << significandBitCount) &- 1
  }
  
  
  // We do not use the high bits of section numbers, to reduce the chance that
  // the `Int64.random(in:)` call in the general-case `while loop` will itself
  // need to call `next()` more than once.
  //
  // Ranges like -1.0...1.0 would otherwise span just over half of all sections,
  // meaning `random(in:)` would on average call `next()` twice. Each bit we
  // do not use effectively halves the probability of a 2nd call to `next()`.
  //
  // We choose to skip 4 bits in order to optimize for Double, which has 52
  // significand bits. Ordinarily, without this optimization, there would be
  // 2^61 section numbers for the 2nd-largest binade in a range, which leaves
  // 9 bits of slack for Double.
  //
  // We take 4 of them here to make choosing a section faster, and leave 5 of
  // them for keeping the sections small. When every representable value in a
  // raw binade lands in a separate section, then we do not need to generate a
  // significand separately because each section has only one value.
  @inline(__always)
  static var sectionScale: Int { 4 }
}
