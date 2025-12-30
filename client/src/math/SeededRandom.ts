/**
 * Deterministic seeded random number generator using xorshift32 algorithm.
 * Critical for P2P lockstep networking - all clients must produce identical sequences.
 */
export class SeededRandom {
  private state: number

  constructor(seed: number) {
    this.state = seed || 1
  }

  /**
   * Returns a random float between 0 (inclusive) and 1 (exclusive)
   */
  next(): number {
    let x = this.state
    x ^= x << 13
    x ^= x >>> 17
    x ^= x << 5
    this.state = x >>> 0
    return (x >>> 0) / 0xffffffff
  }

  /**
   * Returns a random integer from 0 (inclusive) to max (exclusive)
   */
  nextInt(max: number): number {
    return Math.floor(this.next() * max)
  }

  /**
   * Returns a random float in the range [min, max)
   */
  nextRange(min: number, max: number): number {
    return min + this.next() * (max - min)
  }

  /**
   * Returns a random boolean with given probability of true (default 0.5)
   */
  nextBool(probability = 0.5): boolean {
    return this.next() < probability
  }

  /**
   * Returns a random element from an array
   */
  pick<T>(array: readonly T[]): T | undefined {
    if (array.length === 0) return undefined
    return array[this.nextInt(array.length)]
  }

  /**
   * Shuffles an array in place using Fisher-Yates algorithm
   */
  shuffle<T>(array: T[]): T[] {
    for (let i = array.length - 1; i > 0; i--) {
      const j = this.nextInt(i + 1)
      const temp = array[i]!
      array[i] = array[j]!
      array[j] = temp
    }
    return array
  }

  /**
   * Returns the current internal state (for serialization/debugging)
   */
  getSeed(): number {
    return this.state
  }

  /**
   * Creates a copy of this RNG with the same state
   */
  clone(): SeededRandom {
    const copy = new SeededRandom(1)
    copy.state = this.state
    return copy
  }
}
