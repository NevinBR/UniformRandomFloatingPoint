// Author: Nevin Brackett-Rozinsky
//
// This file implements methods to generate random floating-point numbers, with
// probability proportional to the distance between each representable value
// and the next.
//
// In other words, the behavior is as if choosing a real number in a range, and
// rounding down to the next representible value. For closed ranges, we extend
// to a half-open range bounded by upperBound.nextUp
//
// Terminology note: "raw binade" as used in this file refers to the set of
// all floating-point numbers that share the same sign and raw exponent.

extension BinaryFloatingPoint where RawSignificand: FixedWidthInteger {
  // Generate a random floating-point value in a range.
  public static func uniformRandom(in range: Range<Self>) -> Self {
    var generator = SystemRandomNumberGenerator()
    return uniformRandom(in: range, using: &generator)
  }
  
  // Generate a random floating-point value in a range, using a specified
  // random number generator.
  public static func uniformRandom<R: RandomNumberGenerator>(
    in range: Range<Self>, using generator: inout R
  ) -> Self {
    precondition(range.upperBound.isFinite)
    return _uniformRandomRoundedDown(in: range, using: &generator)
  }
  
  // Generate a random floating-point value in a closed range.
  public static func uniformRandom(in range: ClosedRange<Self>) -> Self {
    var generator = SystemRandomNumberGenerator()
    return uniformRandom(in: range, using: &generator)
  }
  
  // Generate a random floating-point value in a closed range, using a specified
  // random number generator.
  public static func uniformRandom<R: RandomNumberGenerator>(
    in range: ClosedRange<Self>, using generator: inout R
  ) -> Self {
    precondition(range.upperBound.isFinite)
    let extendedRange = range.lowerBound ..< range.upperBound.nextUp
    return _uniformRandomRoundedDown(in: extendedRange, using: &generator)
  }
  
  
  // MARK: Implementation details
  
  // Generate a random floating-point value in the specified range, as if a real
  // number were chosen uniformly at random from that range then rounded down to
  // the nearest representable value. An upper bound of infinity is treated as
  // one ulp beyond `greatestFiniteMagnitude`.
  //
  // The general approach is:
  //
  // i) Expand the range so its new bounds are symmetric about 0, and their
  //    significand bits are 0.
  //
  // ii) Divide the expanded range into 2^60 equal-size subintervals, which are
  //     labeled (in order) with consecutive integers.
  //
  // iii) Find the first and last sections that overlap the original range,
  //      call them M and N.
  //
  // iv) Choose an integer uniformly at random between M and N (inclusive).
  //
  // v) Pick a floating-point value uniformly at random from that section.
  //
  //    a. In most sections, all floating-point values have a single raw
  //       exponent, so only a significand needs to be generated.
  //
  //    b. The exceptions are sections with 0 as a bound, where first an
  //       exponent is chosen logarithmically, then a significand uniformly.
  //
  // vi) If the resulting value is contained in the original range, return it.
  //     Otherwise, continue from step iv.
  //
  // This strategy is augmented with special handling for very small ranges, to
  // avoid the scenario where only 1 or 2 sections overlap the range, and most
  // of the values in those sections fall outside the range.
  //
  // To implement the above algorithm, it is necessary to convert back and forth
  // between floating-point values and their corresponding section numbers. For
  // this purpose we utilize the symmetry between floating-point exponents and
  // integer binary logarithms.
  //
  // All integers that occupy a given number of bits, represent sections within
  // a single raw binade. Each raw binade is twice as wide as the previous, and
  // using one more bit produces twice as many integers, so the length of each
  // section stays constant across binades.
  //
  // The integer 0 represents a section which begins at 0 and has the same
  // length as all other sections. Similarly, negative integers represent
  // sections of the same length extending below zero.
  //
  // The following diagram illustrates this:
  //
  // ________________                |                ________________
  //                 ________        |        ________
  //                         ____    |    ____
  //                             __  |  __
  //                               _ | _
  //                                _|_
  //                                 |
  //                                 0
  private static func _uniformRandomRoundedDown<R: RandomNumberGenerator>(
    in range: Range<Self>, using generator: inout R
  ) -> Self {
    precondition(!range.isEmpty)
    precondition(range.lowerBound.isFinite)
    
    // Fast path
    //
    // Simple ranges bounded by the start of a raw binade and either 0 or the
    // negative of the first bound. We expect these ranges will be the most
    // common in practice, as they include 0..<1 and -1..<1.
    let (a, b) = (range.lowerBound, range.upperBound)
    
    if (a.significandBitPattern == 0) && (b.significandBitPattern == 0) {
      let (aExp, bExp) = (a.exponentBitPattern, b.exponentBitPattern)
      
      if aExp == 0 {
        return _randomUpToExponent(bExp, using: &generator)
      } else if a == -b {
        return _randomUpToExponent(bExp, allowNegative: true, using: &generator)
      } else if bExp == 0 {
        return -_randomUpToExponent(aExp, using: &generator).nextUp
      }
    }
    
    // Small range
    //
    // Ranges that cross up to one raw binade boundary are handled here to
    // ensure the `while true` loop in the general case usually succeeds.
    //
    // This only needs to be done when it is possible for more than one
    // representable number in the second-largest raw binade of the range to
    // fall in a single section.
    if significandBitCount > _sectionBitCount &- 3  {
      if let x = _smallRangeUniformRandom(in: range, using: &generator) {
        return x
      }
    }
    
    // General case
    //
    // Expand the range to be centered at 0, with bounds having all significand
    // bits equal to 0. Divide it into 2^60 equal sections, and find which
    // sections intersect the original range.
    let (sections, e) = _sectionsAndExponent(range)
    
    while true {
      let n = Int64.random(in: sections, using: &generator)
      let x = _uniformRandomInSection(n, maxExponent: e, using: &generator)
      if range.contains(x) { return x }
    }
  }
  
  
  // MARK: General case
  
  // Convert a range of Self into a range of Int64 section numbers and the
  // corresponding maximum exponent.
  private static func _sectionsAndExponent(
    _ range: Range<Self>
  ) -> (sections: ClosedRange<Int64>, maxExponent: RawExponent) {
    let (a, b) = (range.lowerBound, range.upperBound)
    
    let m = maximumMagnitude(a, b)
    var e = m.exponentBitPattern
    if m.significandBitPattern != 0 { e += 1 }
    
    let (low, _) = a._sectionNumber(maxExponent: e)
    let (h, isLowerBound) = b._sectionNumber(maxExponent: e)
    let high = isLowerBound ? h &- 1 : h
    return (low...high, e)
  }
  
  // Find which section a floating-point value is in. First subtract its raw
  // exponent from the maximum allowed, to obtain the number of leading zeros
  // in the section number. Then shift its significand bits (including the
  // implicit bit) to that position.
  private func _sectionNumber(
    maxExponent eMax: RawExponent
  ) -> (section: Int64, isLowerBound: Bool) {
    let (e, s) = (exponentBitPattern, significandBitPattern)
    
    precondition(eMax > 0)
    precondition(e <= eMax, "Exponent exceeds maximum")
    
    if self == 0 { return (section: 0, isLowerBound: true) }
    
    var n: UInt64
    let isLowerBound: Bool
    
    let w = Self._sectionBitCount &- 1
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
  
  
  // Choose a random number in a single section.
  //
  // The number of leading zeros in the section number indicates the number of
  // raw binades below maxExponent.
  //
  // Its remaining bits form the implicit bit and the significand of the result.
  // If there are not enough bits in the section number to fill the significand,
  // the low bits are chosen uniformly at random.
  //
  // Section 0 may span multiple raw binades, and is handled specially. Negative
  // sections are nearly mirrors of the positive, but off by one.
  private static func _uniformRandomInSection<R: RandomNumberGenerator>(
    _ section: Int64,
    maxExponent eMax: RawExponent,
    using generator: inout R
  ) -> Self {
    let k = (section < 0) ? ~section : section
    let n = UInt64(bitPattern: k)
    let x: Self
    
    if (n == 0) && (eMax >= _sectionBitCount) {
      // Section 0 spanning at least one full raw binade
      let e = eMax - RawExponent(truncatingIfNeeded: _sectionBitCount &- 1)
      x = _randomUpToExponent(e, using: &generator)
    } else {
      // Each other section fits in a single raw binade
      let z = n.leadingZeroBitCount &- (UInt64.bitWidth - _sectionBitCount)
      precondition(z >= 0)
      
      let isNormal = z < eMax
      let e = isNormal ? eMax - RawExponent(truncatingIfNeeded: z) : 0
      let unusedBitCount = isNormal ? z &+ 1 : Int(truncatingIfNeeded: eMax)
      let availableBitCount = _sectionBitCount &- unusedBitCount
      let shift = significandBitCount &- availableBitCount
      
      var s: RawSignificand
      
      if shift <= 0 {
        s = RawSignificand(truncatingIfNeeded: n >> -shift)
      } else {
        s = generator.next()
        s &= (1 << shift) &- 1
        s |= RawSignificand(truncatingIfNeeded: n) << shift
      }
      
      s &= _significandMask
      x = Self(sign: .plus, exponentBitPattern: e, significandBitPattern: s)
    }
    
    return (section < 0) ? -x.nextUp : x
  }
  
  
  // MARK: Fast path
  
  // Choose a uniformly random representable number with raw exponent less than
  // eMax. If allowNegative is true, then make it negative half the time.
  private static func _randomUpToExponent<R: RandomNumberGenerator>(
    _ eMax: RawExponent,
    allowNegative: Bool = false,
    using generator: inout R
  ) -> Self {
    if eMax == 0 { return 0 }
    
    let e: RawExponent
    var bits: UInt64
    var bitCount: Int
    
    if (exponentBitCount < Int.bitWidth) || (eMax <= Int.max) {
      // eMax fits in an Int, so use the specialized version
      var i = Int(truncatingIfNeeded: eMax)
      (i, bits, bitCount) = _randomExponent(upperBound: i, using: &generator)
      e = RawExponent(truncatingIfNeeded: i)
    } else {
      (e, bits, bitCount) = _randomExponent(upperBound: eMax, using: &generator)
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
    
    s &= _significandMask
    let x = Self(sign: .plus, exponentBitPattern: e, significandBitPattern: s)
    return isNegative ? -x.nextUp : x
  }
  
  
  // Choose a raw exponent less than upperBound, with probability proportional
  // to the width of the raw binade with that raw exponent. Also return any
  // additional random bits that were left over, and a count of how many.
  //
  // This function is generic over T because it is faster for Int, but also
  // needs to work for RawExponent.
  private static func _randomExponent<T, R>(
    upperBound: T,
    using generator: inout R
  ) -> (e: T, bits: UInt64, bitCount: Int)
    where R: RandomNumberGenerator, T: BinaryInteger
  {
    if upperBound <= 1 { return (0, 0, 0) }
    
    var e = upperBound - 1
    var bits: UInt64
    var z: Int
    
    // Each raw binade (except raw exponent 0) is the same width as all those
    // below it. So with 50% probability stop where we are, and otherwise
    // reduce the exponent. Repeat until we stop or reach 0.
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
  private static func _smallRangeUniformRandom<R: RandomNumberGenerator>(
    in range: Range<Self>,
    using generator: inout R
  ) -> Self? {
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
          let span = high &+ (_significandMask &- low)
          let r = RawSignificand.random(in: 0...span, using: &generator)
          isHigh = r < high
          s = isHigh ? r : low &+ (r &- high)
          
        } else if high <= (low &>> 1) {
          // Both normal
          let h2 = high &<< 1
          let span = h2 &+ (_significandMask &- low)
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
  internal static var _significandMask: RawSignificand {
    // We use `<<` in case significandBitCount == RawSignificand.bitwidth
    return (1 << significandBitCount) &- 1
  }
  
  // We do not use the high bits of section numbers, to reduce the chance that
  // the `Int64.random(in:)` call in the general-case will itself need to call
  // `next()` more than once.
  //
  // Ranges like -1.0...1.0 would otherwise span just over half of all sections,
  // meaning `random(in:)` would call `next()` twice on average. Each bit we
  // do not use effectively halves the probability of a 2nd call to `next()`.
  //
  // We choose to skip 4 bits in order to optimize for Double, which has 52
  // significand bits. Ordinarily, without this optimization, there would be
  // 2^61 section numbers for the 2nd-largest binade in a range, which leaves
  // 9 bits of slack for Double.
  //
  // We take 4 of them here to make choosing a section faster and leave 5 of
  // them to keep the sections small, because when each section in a raw binade
  // contains only one value, then we do not need to generate a significand.
  @inline(__always)
  private static var _sectionBitCount: Int { UInt64.bitWidth - 4 }
}
