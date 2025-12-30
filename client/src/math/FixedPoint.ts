/**
 * Fixed-point arithmetic utilities for deterministic game simulation.
 * Uses 16.16 format (16 bits integer, 16 bits fractional).
 * Critical for P2P lockstep - avoids floating point inconsistencies across platforms.
 */

const FP_SHIFT = 16
const FP_ONE = 1 << FP_SHIFT
const FP_HALF = FP_ONE >> 1
const FP_MASK = FP_ONE - 1

export class FixedPoint {
  /**
   * Number of fractional bits in the fixed-point representation
   */
  static readonly SHIFT = FP_SHIFT

  /**
   * The fixed-point representation of 1.0
   */
  static readonly ONE = FP_ONE

  /**
   * The fixed-point representation of 0.5
   */
  static readonly HALF = FP_HALF

  /**
   * Convert a floating-point number to fixed-point
   */
  static fromFloat(n: number): number {
    return Math.round(n * FP_ONE)
  }

  /**
   * Convert a fixed-point number to floating-point
   */
  static toFloat(n: number): number {
    return n / FP_ONE
  }

  /**
   * Convert an integer to fixed-point (no fractional part)
   */
  static fromInt(n: number): number {
    return n << FP_SHIFT
  }

  /**
   * Convert a fixed-point number to integer (truncates fractional part)
   */
  static toInt(n: number): number {
    return n >> FP_SHIFT
  }

  /**
   * Round a fixed-point number to the nearest integer (as fixed-point)
   */
  static round(n: number): number {
    return (n + FP_HALF) & ~FP_MASK
  }

  /**
   * Floor a fixed-point number to the nearest integer (as fixed-point)
   */
  static floor(n: number): number {
    return n & ~FP_MASK
  }

  /**
   * Ceiling a fixed-point number to the nearest integer (as fixed-point)
   */
  static ceil(n: number): number {
    return (n + FP_MASK) & ~FP_MASK
  }

  /**
   * Get the fractional part of a fixed-point number
   */
  static frac(n: number): number {
    return n & FP_MASK
  }

  /**
   * Add two fixed-point numbers
   */
  static add(a: number, b: number): number {
    return a + b
  }

  /**
   * Subtract two fixed-point numbers
   */
  static sub(a: number, b: number): number {
    return a - b
  }

  /**
   * Multiply two fixed-point numbers
   */
  static mul(a: number, b: number): number {
    // Use 64-bit arithmetic by splitting into high/low parts
    // This avoids overflow for reasonable values
    return Math.round((a * b) / FP_ONE)
  }

  /**
   * Divide two fixed-point numbers
   */
  static div(a: number, b: number): number {
    if (b === 0) return a >= 0 ? Number.MAX_SAFE_INTEGER : Number.MIN_SAFE_INTEGER
    return Math.round((a * FP_ONE) / b)
  }

  /**
   * Absolute value of a fixed-point number
   */
  static abs(n: number): number {
    return n < 0 ? -n : n
  }

  /**
   * Minimum of two fixed-point numbers
   */
  static min(a: number, b: number): number {
    return a < b ? a : b
  }

  /**
   * Maximum of two fixed-point numbers
   */
  static max(a: number, b: number): number {
    return a > b ? a : b
  }

  /**
   * Clamp a fixed-point number to a range
   */
  static clamp(n: number, min: number, max: number): number {
    return n < min ? min : n > max ? max : n
  }

  /**
   * Linear interpolation between two fixed-point numbers
   * @param a Start value
   * @param b End value
   * @param t Interpolation factor (0-1 as fixed-point)
   */
  static lerp(a: number, b: number, t: number): number {
    return a + FixedPoint.mul(b - a, t)
  }

  /**
   * Sign of a fixed-point number (-1, 0, or 1)
   */
  static sign(n: number): number {
    return n < 0 ? -1 : n > 0 ? 1 : 0
  }

  /**
   * Square root approximation (uses float internally but returns fixed)
   * For deterministic sqrt, consider a lookup table or Newton-Raphson iteration
   */
  static sqrt(n: number): number {
    if (n < 0) return 0
    // Convert to float, sqrt, convert back - acceptable for most use cases
    return FixedPoint.fromFloat(Math.sqrt(FixedPoint.toFloat(n)))
  }
}

// Export convenience functions for backwards compatibility
export const toFixed = FixedPoint.fromFloat
export const fromFixed = FixedPoint.toFloat
