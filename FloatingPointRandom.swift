// Author: Nevin Brackett-Rozinsky
//
// This is a proof-of-concept implementation to generate random floating-point
// numbers, with probability proportional to the distance between each
// representable value and the next. In other words, the behavior is as if
// choosing a real number in the range, and rounding down to the next
// representible value. For closed ranges, we extend it into a half-open range
// bounded by upperBound.nextUp

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
    // .greatestFinityMagnitude
    
    // If the size of the range, counted in terms of the smallest ulp in the
    // range, fits in a RawSignificand, then we can choose a value directly.
    if let x = smallRangeUniformRandom(in: range, using: &generator) {
      return x
    }
    
    // Otherwise, take the smallest range centered at 0 with bounds having raw
    // significand equal to 0, which contains the target range, and divide it
    // into 2^64 equal sections. Find which section the bounds of the original
    // range land in, and choose a section at random between them (inclusive).
    //
    // That section either has all values (except possibly one bound) with the
    // same raw exponent, or else it has one bound at 0 and the other with raw
    // significand 0.
    //
    // In either case, use a helper function to choose a random number
    // uniformly within that section. If the result is within the original
    // range, return that value. Otherwise choose a new section and repeat.
    
    let (a, b) = (range.lowerBound, range.upperBound)
    let e = max(abs(a), abs(b)).nextDown.exponentBitPattern &+ 1
    
    // Find section numbers
    let low = a.integerPosition(maxExponent: e)
    let h1 = b.integerPosition(maxExponent: e) &- 1
    let h2 = b.nextDown.integerPosition(maxExponent: e)
    let high = max(h1, h2)
    
    while true {
      let n = Int64.random(in: low...high, using: &generator)
      let s = bounds(ofSection: n, maxExponent: e)
      let x = uniformRandomInSection(s, using: &generator)
      if range.contains(x) { return x }
    }
  }
  
  
  // MARK: Small range
  
  // Small ranges come in many shapes. First, consider how many spare
  // bits are in the RawSignificand type. That puts an upper bound on the
  // number of full binades that can be handled at once.
  //
  // If the range crosses 0, then distances are counted in terms of the ulp of
  // 0, which is .leastNonzeroMagnitude. In this case, the raw exponents must
  // be less than the number of spare bits.
  //
  // If the range does not cross zero, then the distances are counted in terms
  // of the ulp of the smaller-magnitude bound, and the difference in raw
  // exponents must be less than the number of spare bits. One exception is
  // when the lesser bound is subnormal, in which case the difference in raw
  // exponents can be equal to the number of spare bits.
  //
  // If there are no spare bits at all, meaning that all the bits of the
  // RawSignificand type are utilized, then the standard approach breaks down
  // outside of a single binade.
  //
  // However, if the bounds are in adjacent binades and the significands are
  // close enough to the boundary of those binades, then we can still measure
  // the distance between them in terms of the smaller ulp.
  static func smallRangeUniformRandom<R: RandomNumberGenerator>(in range: Range<Self>, using generator: inout R) -> Self? {
    let (a, b) = (range.lowerBound, range.upperBound)
    let (aMag, bMag) = (a.magnitude, b.magnitude)
    let (mMin, mMax) = (aMag < bMag) ? (aMag, bMag) : (bMag, aMag)
    let (eMin, eMax) = (mMin.exponentBitPattern, mMax.nextDown.exponentBitPattern)
    let (sMin, sMax) = (mMin.significandBitPattern, mMax.nextDown.significandBitPattern)
    
    let isSameSign = (a.sign == b.sign) || (mMin == 0)
    
    if isSameSign {
      let sign: FloatingPointSign = (a == 0) ? .plus : a.sign
      
      if eMax == eMin {
        // Single binade
        let n = RawSignificand.random(in: sMin...sMax, using: &generator)
        let x = Self(sign: sign, exponentBitPattern: eMin, significandBitPattern: n)
        return (sign == .plus) ? x : x.nextDown
        
      } else if (eMax &- eMin < spareBitCount) || (eMax == spareBitCount)  {
        // One-sided small range
        let low = mMin.positionInSmallPositiveRange(minExponent: eMin)
        let high = mMax.positionInSmallPositiveRange(minExponent: eMin) &- 1
        let r = RawSignificand.random(in: low...high, using: &generator)
        let x = positiveValueAtPosition(r, minExponent: eMin)
        return (sign == .plus) ? x : (-x).nextDown
        
      } else if (eMax == 1) && (sMax < sMin) {
        // Adjacent binades (one subnormal), no spare bits
        let high = sMax &- sMin
        let r = RawSignificand.random(in: 0...high, using: &generator)
        let n = sMin &+ r
        let e = (n < sMin) ? eMax : eMin
        let x = Self(sign: sign, exponentBitPattern: e, significandBitPattern: n)
        return (sign == .plus) ? x : x.nextDown
        
      } else if (eMax == eMin &+ 1) && (sMax < sMin &>> 1) {
        // Adjacent binades (normal), no spare bits
        let high = (sMax &<< 1) &+ 1 &- sMin
        let r = RawSignificand.random(in: 0...high, using: &generator)
        let n = sMin &+ r
        let e = (n < sMin) ? eMax : eMin
        let s = (n < sMin) ? n &>> 1 : n
        let x = Self(sign: sign, exponentBitPattern: e, significandBitPattern: s)
        return (sign == .plus) ? x : x.nextDown
      }
      
    } else if eMax < spareBitCount {
      // Two-sided small range
      let low = a.positionInSmallRange()
      let high = b.positionInSmallRange() &- 1
      let r = RawSignificand.random(in: low...high, using: &generator)
      return valueAtPosition(r)
      
    } else if (eMax == 0) && (sMin &+ sMax >= sMax) {
      // Two-sided subnormals, no spare bits
      let high = sMin &+ sMax
      let r = RawSignificand.random(in: 0...high, using: &generator)
      let threshold = b.significandBitPattern &- 1
      let sign: FloatingPointSign = (r > threshold) ? .minus : .plus
      let n = (sign == .plus) ? r : (r &- threshold)
      return Self(sign: sign, exponentBitPattern: 0, significandBitPattern: n)
    }
    
    return nil
  }
  
  
  // Two-sided small ranges (ie. crossing 0), counting distance in terms of
  // the ulp of 0 (aka. leastNonzeroMagnitude).
  func positionInSmallRange() -> RawSignificand {
    let highBit = Self.significandHighBit
    let n = self.positionInSmallPositiveRange(minExponent: 0)
    precondition(n <= highBit)
    return (self < 0) ? (highBit &- n) : (n ^ highBit)
  }
  
  
  // Non-negative small ranges, counting distance in terms of the ulp of the
  // lower bound. The
  func positionInSmallPositiveRange(minExponent: RawExponent) -> RawSignificand {
    precondition(exponentBitPattern >= minExponent)
    if exponentBitPattern == 0 { return significandBitPattern }
    let shift = exponentBitPattern &- max(1, minExponent)
    
    // The just-beyond-the-end position wraps around to zero.
    if (shift == Self.spareBitCount) && (significandBitPattern == 0) {
      return 0
    }
    
    precondition(Self.spareBitCount > shift)
    return (Self.uncheckedImplicitBit | significandBitPattern) &<< shift
  }
  
  
  // Counting in terms of the ulp of 0 (aka. leastNonzeroMagnitude)
  static func valueAtPosition(_ p: RawSignificand) -> Self {
    let highBit = significandHighBit
    let isNegative = (p & highBit) == 0
    
    if isNegative {
      let n = highBit &- 1 &- p
      let r = positiveValueAtPosition(n, minExponent: 0)
      return (-r).nextDown
    } else {
      let n = p ^ highBit
      return positiveValueAtPosition(n, minExponent: 0)
    }
  }
  
  
  // Counting in terms of the ulp of the binade with exponent minExponent.
  // The result must have raw exponent of minExponent or greater.
  static func positiveValueAtPosition(_ p: RawSignificand, minExponent: RawExponent) -> Self {
    let z = p.leadingZeroBitCount
    
    if z < spareBitCount {
      let shift = spareBitCount &- 1 &- z
      let s = (p &>> shift) & significandBitMask
      let e = RawExponent(truncatingIfNeeded: shift) &+ max(1, minExponent)
      return Self(sign: .plus, exponentBitPattern: e, significandBitPattern: s)
    } else {
      precondition(minExponent == 0)
      return Self(sign: .plus, exponentBitPattern: 0, significandBitPattern: p)
    }
  }
  
  
  // MARK: Large range
  
  // Take the range with bounds having raw exponent equal to maxExponent and
  // 0 significand, and split it into 2^64 sections. Find which section self
  // falls in.
  func integerPosition(maxExponent eMax: RawExponent) -> Int64 {
    let (e, s) = (exponentBitPattern, significandBitPattern)
    
    if (e == eMax) && (s == 0) {
      return (self < 0) ? .min : .max
    }
    
    precondition(e < eMax, "Exponent exceeds maximum")
    
    if self < 0 {
      let n1 = self.integerPositionPositive(maxExponent: eMax) &- 1
      let n2 = self.nextUp.integerPositionPositive(maxExponent: eMax)
      let n = max(Int64(truncatingIfNeeded: n1), Int64(truncatingIfNeeded: n2))
      return -1 &- n
    }
    
    let n = integerPositionPositive(maxExponent: eMax)
    return Int64(truncatingIfNeeded: n)
  }
  
  
  // Take the range with lower bound 0 and upper bound having raw exponent
  // equal to maxExponent+1 and 0 significand, and split it into 2^64 sections.
  // Find which section the absolute value of self falls in.
  func integerPositionPositive(maxExponent eMax: RawExponent) -> UInt64 {
    let (e, s) = (exponentBitPattern, significandBitPattern)
    
    precondition(eMax > 0)
    precondition(e <= eMax, "Exponent exceeds maximum")
    
    let w = UInt64.bitWidth
    let z = eMax &- max(1, e)
    
    if z >= w {
      if (e != 0) && (z == w) { return 1 }
      return 0
    }
    
    let bitsNeeded = w &- 1 &- Int(truncatingIfNeeded: z)
    let shift = bitsNeeded &- Self.significandBitCount
    let n: UInt64
    
    if shift < 0 {
      n = UInt64(truncatingIfNeeded: s &>> -shift)
    } else {
      n = UInt64(truncatingIfNeeded: s) &<< shift
    }
    
    if e == 0 { return n }
    return n | (1 &<< bitsNeeded)
  }
  
  
  static func bounds(ofSection n: Int64, maxExponent eMax: RawExponent) -> Range<Self> {
    let a = lowerBound(ofSection: n, maxExponent: eMax)
    let b = lowerBound(ofSection: n &+ 1, maxExponent: eMax)
    if n == .max { return a ..< -b }
    return a ..< b
  }
  
  
  static func lowerBound(ofSection n: Int64, maxExponent eMax: RawExponent) -> Self {
    if (n == 0) || (eMax == 0) { return 0 }
    
    let w = UInt64.bitWidth
    let m = n.magnitude
    let z = m.leadingZeroBitCount
    let isNormal = z < eMax
    
    let sign: FloatingPointSign = (n < 0) ? .minus : .plus
    let e = isNormal ? eMax &- RawExponent(truncatingIfNeeded: z) : 0
    
    let unusedBitCount = isNormal ? z &+ 1 : Int(truncatingIfNeeded: eMax)
    let availableBitCount = w &- unusedBitCount
    let shift = significandBitCount &- availableBitCount
    
    let sigBits: RawSignificand
    var needNextDown = false
    
    if shift < 0 {
      var k = m
      if sign == .minus {
        k = m &- 1
        needNextDown = true
      }
      sigBits = RawSignificand(truncatingIfNeeded: k &>> -shift)
    } else {
      sigBits = RawSignificand(truncatingIfNeeded: m) &<< shift
    }
    
    let s = sigBits & significandBitMask
    let x = Self(sign: sign, exponentBitPattern: e, significandBitPattern: s)
    return needNextDown ? x.nextDown : x
  }
  
  
  // Get a random number in a single section (as defined above). Specifically,
  // either the entire range (except possibly the greater-magnitude bound) must
  // have the same raw exponent, or one bound must be zero and the other must
  // have raw significand equal to zero.
  static func uniformRandomInSection<R: RandomNumberGenerator>(_ range: Range<Self>, using generator: inout R) -> Self {
    if let x = randomInSingleBinade(range, using: &generator) {
      return x
    }
    
    let (a, b) = (range.lowerBound, range.upperBound)
    
    precondition((a == 0) || (b == 0), "Unexpected nonzero bound")
    precondition(a.significandBitPattern == 0, "Unexpected nonzero significand")
    precondition(b.significandBitPattern == 0, "Unexpected nonzero significand")
    
    let maxExp = max(a.exponentBitPattern, b.exponentBitPattern)
    let x = randomUpToExponent(maxExp, using: &generator)
    if a < 0 { return (-x).nextDown }
    return x
  }
  
  
  static func randomInSingleBinade<R: RandomNumberGenerator>(_ range: Range<Self>, using generator: inout R) -> Self? {
    let (a, b) = (range.lowerBound, range.upperBound)
    if range.isEmpty { return a }
    
    if a < 0 {
      guard let x = randomInSinglePositiveBinade(abs(b) ..< abs(a), using: &generator) else {
        return nil
      }
      return (-x).nextDown
    }
    return randomInSinglePositiveBinade(a ..< b, using: &generator)
  }
  
  
  static func randomInSinglePositiveBinade<R: RandomNumberGenerator>(_ range: Range<Self>, using generator: inout R) -> Self? {
    guard range.lowerBound >= 0 else { return nil }
    if range.isEmpty { return range.lowerBound }
    guard isInSinglePositiveBinade(range) else { return nil }
    
    let (a, b) = (range.lowerBound, range.upperBound.nextDown)
    if a == b { return a }
    
    let low = a.significandBitPattern
    let high = b.significandBitPattern
    
    let n = RawSignificand.random(in: low...high, using: &generator)
    let e = a.exponentBitPattern
    return Self(sign: .plus, exponentBitPattern: e, significandBitPattern: n)
  }
  
  
  static func isInSinglePositiveBinade(_ range: Range<Self>) -> Bool {
    precondition(range.lowerBound >= 0, "Range must be non-negative")
    if range.isEmpty { return true }
    
    let (a, b) = (range.lowerBound, range.upperBound)
    let (aExp, bExp) = (a.exponentBitPattern, b.exponentBitPattern)
    
    if aExp == bExp { return true }
    return (aExp &+ 1 == bExp) && (b.significandBitPattern == 0)
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
      if n < z { return 0 }
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
