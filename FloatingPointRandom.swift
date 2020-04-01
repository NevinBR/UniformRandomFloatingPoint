// Author: Nevin Brackett-Rozinsky
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
    
    let (a, b) = (range.lowerBound, range.upperBound)
    
    if R.self != SystemRandomNumberGenerator.self {
      if (a.significandBitPattern == 0) && (b.significandBitPattern == 0) {
        // Fast path for simple ranges
        if a.exponentBitPattern == 0 {
          return randomUpToExponent(b.exponentBitPattern, using: &generator)
        } else if a == -b {
          let x = randomUpToExponent(b.exponentBitPattern, using: &generator)
          return Bool.random(using: &generator) ? x : (-x).nextDown
        } else if b.exponentBitPattern == 0 {
          let x = randomUpToExponent(a.exponentBitPattern, using: &generator)
          return (-x).nextDown
        }
      }
    }
    
    if significandBitCount > Int64.bitWidth - 3 {
      // Small ranges that cross raw binade boundaries need to be handled
      // separately to ensure the `while true` loop below usually succeeds.
      if let x = smallRangeUniformRandom(in: range, using: &generator) {
        return x
      }
    }
    
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
    
    let m = maximumMagnitude(a, b)
    let mExp = m.exponentBitPattern
    let e = (m.significandBitPattern == 0) ? mExp : mExp &+ 1
    
    let (low, _) = a.sectionNumber(maxExponent: e)
    let (h, isLowerBound) = b.sectionNumber(maxExponent: e)
    let high = isLowerBound ? h &- 1 : h
    
    while true {
      let s = Int64.random(in: low...high, using: &generator)
      let x = uniformRandomInSection(s, maxExponent: e, using: &generator)
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
  // that probability is less than 1 in 2^60 in the worst case.
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
    
    if z >= w {
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
    
    if (n == 0) && (eMax >= w) {
      // Section 0 spanning at least one full raw binade
      let e = eMax &- RawExponent(truncatingIfNeeded: w &- 1)
      x = randomUpToExponent(e, using: &generator)
    } else {
      // Every other section fits in a single raw binade
      let z = n.leadingZeroBitCount
      let isNormal = z < eMax
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
        //
        // Perhaps the compiler can eliminate the check during specialization,
        // or maybe it would be able to if written:
        //    (spareBitCount != 0) || (shift < RawSignificand.bitWidth)
        // instead?
        if shift < RawSignificand.bitWidth {
          s &= (1 &<< shift) &- 1
          s |= RawSignificand(truncatingIfNeeded: n) &<< shift
        }
      }
      
      s &= significandBitMask
      x = Self(sign: .plus, exponentBitPattern: e, significandBitPattern: s)
    }
    
    return (section < 0) ? (-x).nextDown : x
  }
  
  
  static func randomUpToExponent<R: RandomNumberGenerator>(_ maxExp: RawExponent, using generator: inout R) -> Self {
    if maxExp == 0 { return 0 }
    let e = randomExponent(upperBound: maxExp, using: &generator)
    let n = randomSignificand(using: &generator)
    return Self(sign: .plus, exponentBitPattern: e, significandBitPattern: n)
  }
  
  
  static func randomExponent<R: RandomNumberGenerator>(upperBound: RawExponent, using generator: inout R) -> RawExponent {
    if upperBound <= 1 { return 0 }
    var n = upperBound &- 1
    
    while true {
      let r = generator.next()
      let z = r.leadingZeroBitCount
      if n <= z { return 0 }
      n &-= RawExponent(truncatingIfNeeded: z)
      if r != 0 { return n }
    }
  }
  
  static func randomSignificand<R: RandomNumberGenerator>(using generator: inout R) -> RawSignificand {
    return generator.next() & significandBitMask
  }
  
  static var significandBitMask: RawSignificand {
    return (spareBitCount == 0) ? .max : (uncheckedImplicitBit &- 1)
  }
  
  static var spareBitCount: Int {
    return RawSignificand.bitWidth &- significandBitCount
  }
  
  static var uncheckedImplicitBit: RawSignificand {
    return 1 &<< significandBitCount
  }
  
  static var significandHighBit: RawSignificand {
    return (1 as RawSignificand) &<< (RawSignificand.bitWidth &- 1)
  }
}
