// Author: Nevin Brackett-Rozinsky, with help from Jens Persson (@jens-bc)
//
// This is a proof-of-concept implementation to generate random floating-point
// numbers, with probability proportional to the distance between each
// representable value and the next. In other words, the behavior is as if
// choosing a real number in the range, and rounding down to the next
// representible value. For closed ranges, we extend it into a half-open range
// bounded by upperBound.nextUp

// Note on terminology: this file uses "binade" pervasively to refer to the
// set of all floating-point values with the same sign and raw exponent. When
// the word "binade" appears below, it has that meaning. The implementation
// cares about values with the same raw exponent, and the word "binade" is
// repurposed for that definition here.

extension BinaryFloatingPoint where RawSignificand: FixedWidthInteger, RawExponent: FixedWidthInteger {
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
  
  // The base case is small ranges, where the distance between the bounds, when
  // counted in terms of the smallest ulp in the range, fits in an instance of
  // the RawSignificand type without overflowing. In that case, an integer can
  // be chosen in the appropriate range, and the result generated directly.
  //
  // In the general case of a large range where that is not possible, the
  // strategy is as follows:
  //
  // Expand the range so its bounds are equal and opposite powers of 2, ie.
  // -2^n ..< 2^n, considered as a range of real numbers. Split that range into
  // 2^64 equal sections, and find which sections the minimum and maximum values
  // of the original range land in, counting sections from least to greatest.
  //
  // Choose a section between them (inclusive). The bounds of that section are
  // either in the same binade, or adjacent binades with one bound having
  // significand 0, or one bound is exactly 0 and the other bound has
  // significand 0.
  //
  // In the first two cases, a random significand can be chosen directly. In
  // the last case, a simple algorithm is used to choose a random value up to
  // a binade.
  //
  // Having selected a value within the section, if it is also in the original
  // range then we are done. Otherwise, repeat the process of choosing a
  // section and a value within it.
  //
  // The result is a value equivalent to picking a real number uniformly at
  // random within the original range, then rounding down to the nearest
  // representable floating-point number.
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
    // Ranges that cross one raw binade boundary need to be handled separately
    // to ensure the `while true` loop in the general case usually succeeds.
    //
    // The number 3 is subtracted because the 2nd-largest raw binade spans
    // 1/8 of the extended range (or more for subnormals). If the significand
    // is small enough that every value in that binade falls in a different
    // section, then we do not need to handle small ranges separately.
    
    if significandBitCount > Int64.bitWidth - 3 {
      if let x = smallRangeUniformRandom(in: range, using: &generator) {
        return x
      }
    }
    
    
    // General case
    //
    // Take the smallest range centered at 0 with bounds having raw significand
    // equal to 0, which contains the target range, and divide it into 2^64
    // equal sections. Find which section the bounds of the original range land
    // in, and choose a section at random between them (inclusive).
    //
    // That section either has all values (except possibly one bound) with the
    // same raw exponent, or else it has one bound at 0 and the other with raw
    // significand 0.
    //
    // In either case, choose a random number uniformly within that section.
    // If the result is within the original range, return that value.
    // Otherwise choose a new section and repeat.
    
    let (sections, e) = sectionsAndExponent(for: range)
    
    while true {
      let n = Int64.random(in: sections, using: &generator)
      let x = uniformRandomInSection(n, maxExponent: e, using: &generator)
      if range.contains(x) { return x }
    }
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
  // that probability is less than 1 in 2^55 in the worst case.
  static func smallRangeUniformRandom<R: RandomNumberGenerator>(in range: Range<Self>, using generator: inout R) -> Self? {
    let (a, b) = (range.lowerBound, range.upperBound)
    let aExp = a.exponentBitPattern
    let bExp = b.exponentBitPattern
    
    if a.sign == b.sign {
      let sign = a.sign
      let eSpan = (sign == .plus) ? (bExp &- aExp) : (aExp &- bExp)
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
          let span = high &+ (significandBitMask &- low)
          let r = RawSignificand.random(in: 0...span, using: &generator)
          isHigh = r < high
          s = isHigh ? r : low &+ (r &- high)
          
        } else if high <= (low &>> 1) {
          // Both normal
          let h2 = high &<< 1
          let span = h2 &+ (significandBitMask &- low)
          let r = RawSignificand.random(in: 0...span, using: &generator)
          isHigh = r < h2
          s = isHigh ? (r &>> 1) : low &+ (r &- h2)
          
        } else {
          // Large range
          return nil
        }
        
        let e = isHigh ? eBase &+ 1 : eBase
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
  
  
  // MARK: Large range
  
  // Convert a range of Self into a range of Int64 section numbers and the
  // corresponding maximum exponent.
  @inline(__always)
  static func sectionsAndExponent(for range: Range<Self>) -> (sections: ClosedRange<Int64>, maxExponent: RawExponent) {
    let (a, b) = (range.lowerBound, range.upperBound)
    let m = maximumMagnitude(a, b)
    
    // We increase the exponent, if possible, to reduce the chance that the
    // `Int64.random(in:)` call will need to generate more than one value.
    // For example, in cases like -1...1 the range would otherwise span just
    // over half of all sections.
    //
    // If and when the system random number generator becomes fast enough that
    // this optimization can be removed, it will still be necessary to add 1
    // to m.exponentBitPattern, unless m.significandBitPattern == 0.
    let e: RawExponent
    if exponentBitCount > 2 {
      let d = min(5, infinity.exponentBitPattern &- m.exponentBitPattern)
      e = m.exponentBitPattern &+ d
    } else {
      e = infinity.exponentBitPattern
    }
    
    let (low, _) = a.sectionNumber(maxExponent: e)
    let (h, isLowerBound) = b.sectionNumber(maxExponent: e)
    let high = isLowerBound ? h &- 1 : h
    return (low...high, e)
  }
  
  
  // Take the range with bounds having raw exponent equal to maxExponent and
  // 0 significand, and split it into 2^64 sections. Find which section self
  // falls in.
  func sectionNumber(maxExponent eMax: RawExponent) -> (section: Int64, isLowerBound: Bool) {
    let (e, s) = (exponentBitPattern, significandBitPattern)
    
    if (e == eMax) && (s == 0) {
      return (self < 0) ? (.min, true) : (.max, false)
    }
    
    precondition(e < eMax, "Exponent exceeds maximum")
    
    let (n, isLowerBound) = self.unsignedSectionNumber(maxExponent: eMax)
    var section = Int64(bitPattern: n)
    
    if self < 0 {
      section = isLowerBound ? -section : ~section
    }
    
    return (section, isLowerBound)
  }
  
  
  // Take the range with lower bound 0 and upper bound having raw exponent
  // equal to maxExponent+1 and 0 significand, and split it into 2^64 sections.
  // Find which section the absolute value of self falls in.
  func unsignedSectionNumber(maxExponent eMax: RawExponent) -> (section: UInt64, isLowerBound: Bool) {
    let (e, s) = (exponentBitPattern, significandBitPattern)
    
    precondition(eMax > 0)
    precondition(e <= eMax, "Exponent exceeds maximum")
    
    if self == 0 { return (section: 0, isLowerBound: true) }
    
    let w = UInt64.bitWidth
    let z = eMax &- max(1, e)   // Number of leading zeros before implicit bit
    
    if z >= w {                 // Heterogeneous compare (common)
      if (e != 0) && (z == w) { return (1, s == 0) }
      return (0, false)
    }
    
    let bitsNeeded = w &- 1 &- Int(truncatingIfNeeded: z)
    let shift = bitsNeeded &- Self.significandBitCount
    
    let n: UInt64
    let isLowerBound: Bool
    
    if shift < 0 {
      let usableBits = s &>> -shift
      isLowerBound = s == (usableBits &<< -shift)
      n = UInt64(truncatingIfNeeded: usableBits)
    } else {
      n = UInt64(truncatingIfNeeded: s) &<< shift
      isLowerBound = true
    }
    
    if e == 0 { return (n, isLowerBound) }
    
    let section = n | (1 &<< bitsNeeded)
    return (section, isLowerBound)
  }
  
  
  // Get a random number in a single section (as defined above).
  static func uniformRandomInSection<R: RandomNumberGenerator>(_ section: Int64, maxExponent eMax: RawExponent, using generator: inout R) -> Self {
    let n = UInt64(bitPattern: (section < 0) ? ~section : section)
    let w = UInt64.bitWidth
    let x: Self
    
    if (n == 0) && (eMax >= w) {            // Heterogeneous compare (rare)
      // Section 0 spanning at least one full raw binade
      let e = eMax &- RawExponent(truncatingIfNeeded: w &- 1)
      x = randomUpToExponent(e, using: &generator)
    } else {
      // Every other section fits in a single raw binade
      let z = n.leadingZeroBitCount
      let isNormal = z < eMax               // Heterogeneous compare (common)
      let e = isNormal ? eMax &- RawExponent(truncatingIfNeeded: z) : 0
      
      let unusedBitCount = isNormal ? z &+ 1 : Int(truncatingIfNeeded: eMax)
      let availableBitCount = w &- unusedBitCount
      let shift = significandBitCount &- availableBitCount
      
      var s: RawSignificand
      
      if shift <= 0 {
        s = RawSignificand(truncatingIfNeeded: n &>> -shift)
      } else {
        s = generator.next()
        
        // This condition is always true for types with at least 1 spare
        // significand bit, including Float, Double, and Float80.
        // Note that `shift <= significandBitCount` is always true.
        if (spareBitCount != 0) || (shift < significandBitCount) {
          s &= (1 &<< shift) &- 1
          s |= RawSignificand(truncatingIfNeeded: n) &<< shift
        }
      }
      
      s &= significandBitMask
      x = Self(sign: .plus, exponentBitPattern: e, significandBitPattern: s)
    }
    
    return (section < 0) ? -x.nextUp : x
  }
  
  
  // MARK: Fast path
  
  @inline(__always)
  static func randomUpToExponent<R: RandomNumberGenerator>(_ maxExp: RawExponent, allowNegative: Bool = false, using generator: inout R) -> Self {
    if maxExp == 0 { return 0 }
    
    let e: RawExponent
    var bits: UInt64
    var bitCount: Int
    
    if (exponentBitCount < Int.bitWidth) || (maxExp._binaryLogarithm() < Int.bitWidth &- 1) {
      // maxExp fits in an Int, so use the specialized version
      var eInt = Int(truncatingIfNeeded: maxExp)
      (eInt, bits, bitCount) = randomExponent(upperBound: eInt, using: &generator)
      e = RawExponent(truncatingIfNeeded: eInt)
    } else {
      (e, bits, bitCount) = randomExponent(upperBound: maxExp, using: &generator)
    }
    
    let shortOnBits = bitCount < significandBitCount
    let s: RawSignificand
    
    if shortOnBits {
      let r = generator.next() as RawSignificand
      
      if spareBitCount != 0 {
        // Save one bit for later. Technically we only need to do this if
        // allowNegative is true and bitCount is 0.
        bits = (r & uncheckedImplicitBit) == 0 ? 0 : 1
        bitCount = 1
      }
      s = r & significandBitMask

    } else {
      s = RawSignificand(truncatingIfNeeded: bits) & significandBitMask
      bitCount &-= significandBitCount
    }
    
    let x = Self(sign: .plus, exponentBitPattern: e, significandBitPattern: s)
    if !allowNegative { return x }
    
    let isNegative: Bool
    
    if bitCount == 0 {
      isNegative = Bool.random(using: &generator)
    } else {
      let nextBit: UInt64 = shortOnBits ? 1 : 1 &<< significandBitCount
      isNegative = (bits & nextBit) == 0
    }
    return isNegative ? -x.nextUp : x
  }
  
  
  // This function is generic over T because it is faster when specialized for
  // Int. The alternative was to have two copies, one for Int alone and the
  // other for RawExponent. Making it generic avoids that duplication.
  @inline(__always)
  @_specialize(kind: partial, where T == Int)
  static func randomExponent<R: RandomNumberGenerator, T: FixedWidthInteger>(upperBound: T, using generator: inout R) -> (e: T, bits: UInt64, bitCount: Int) {
    if upperBound <= 1 { return (0, 0, 0) }
    
    var e = upperBound &- 1
    var bits: UInt64
    var z: Int
    
    repeat {
      bits = generator.next()
      z = bits.leadingZeroBitCount
      if e <= z { e = 0; break }      // Heterogeneous compare (unless T == Int)
      e &-= T(truncatingIfNeeded: z)
    } while bits == 0
    
    let bitCount = (bits == 0) ? 0 : (UInt64.bitWidth &- 1) &- z
    return (e, bits, bitCount)
  }
  
  
  // MARK: Helper methods
  
  @inline(__always)
  static var significandBitMask: RawSignificand {
    return (spareBitCount == 0) ? .max : (uncheckedImplicitBit &- 1)
  }
  
  @inline(__always)
  static var spareBitCount: Int {
    return RawSignificand.bitWidth &- significandBitCount
  }
  
  @inline(__always)
  static var uncheckedImplicitBit: RawSignificand {
    return 1 &<< significandBitCount
  }
  
  @inline(__always)
  static var significandHighBit: RawSignificand {
    return (1 as RawSignificand) &<< (RawSignificand.bitWidth &- 1)
  }
}
