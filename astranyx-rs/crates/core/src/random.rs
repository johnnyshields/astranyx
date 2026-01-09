//! Deterministic seeded random number generator.
//!
//! Uses xorshift32 algorithm for fast, deterministic pseudo-random numbers.
//! Critical for P2P lockstep networking - all clients must produce identical sequences.

use bincode::{Decode, Encode};
use serde::{Deserialize, Serialize};

/// Deterministic seeded random number generator using xorshift32 algorithm.
#[derive(Debug, Clone, Serialize, Deserialize, Encode, Decode)]
pub struct SeededRandom {
    state: u32,
}

impl SeededRandom {
    /// Creates a new RNG with the given seed.
    /// Seed of 0 is treated as 1 to avoid degenerate sequence.
    pub fn new(seed: u32) -> Self {
        Self {
            state: if seed == 0 { 1 } else { seed },
        }
    }

    /// Returns a random float between 0 (inclusive) and 1 (exclusive).
    pub fn next(&mut self) -> f32 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        self.state = x;
        (x as f32) / (u32::MAX as f32)
    }

    /// Returns the raw u32 value from the RNG.
    pub fn next_u32(&mut self) -> u32 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        self.state = x;
        x
    }

    /// Returns a random integer from 0 (inclusive) to max (exclusive).
    pub fn next_int(&mut self, max: u32) -> u32 {
        ((self.next_u32() as u64 * max as u64) >> 32) as u32
    }

    /// Returns a random float in the range [min, max).
    pub fn next_range(&mut self, min: f32, max: f32) -> f32 {
        min + self.next() * (max - min)
    }

    /// Returns a random boolean with given probability of true (default 0.5).
    pub fn next_bool(&mut self, probability: f32) -> bool {
        self.next() < probability
    }

    /// Returns a random element from a slice.
    pub fn pick<'a, T>(&mut self, slice: &'a [T]) -> Option<&'a T> {
        if slice.is_empty() {
            None
        } else {
            Some(&slice[self.next_int(slice.len() as u32) as usize])
        }
    }

    /// Shuffles a slice in place using Fisher-Yates algorithm.
    pub fn shuffle<T>(&mut self, slice: &mut [T]) {
        for i in (1..slice.len()).rev() {
            let j = self.next_int((i + 1) as u32) as usize;
            slice.swap(i, j);
        }
    }

    /// Returns the current internal state (for serialization/debugging).
    pub fn seed(&self) -> u32 {
        self.state
    }

    /// Sets the internal state directly.
    pub fn set_seed(&mut self, seed: u32) {
        self.state = if seed == 0 { 1 } else { seed };
    }
}

impl Default for SeededRandom {
    fn default() -> Self {
        Self::new(1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic_sequence() {
        let mut rng1 = SeededRandom::new(12345);
        let mut rng2 = SeededRandom::new(12345);

        for _ in 0..1000 {
            assert_eq!(rng1.next_u32(), rng2.next_u32());
        }
    }

    #[test]
    fn different_seeds_different_sequence() {
        let mut rng1 = SeededRandom::new(12345);
        let mut rng2 = SeededRandom::new(54321);

        // Very unlikely to match
        assert_ne!(rng1.next_u32(), rng2.next_u32());
    }

    #[test]
    fn next_int_bounds() {
        let mut rng = SeededRandom::new(42);
        for _ in 0..1000 {
            let val = rng.next_int(10);
            assert!(val < 10);
        }
    }

    #[test]
    fn next_range_bounds() {
        let mut rng = SeededRandom::new(42);
        for _ in 0..1000 {
            let val = rng.next_range(5.0, 10.0);
            assert!(val >= 5.0 && val < 10.0);
        }
    }

    #[test]
    fn shuffle_preserves_elements() {
        let mut rng = SeededRandom::new(42);
        let mut arr = vec![1, 2, 3, 4, 5];
        rng.shuffle(&mut arr);
        arr.sort();
        assert_eq!(arr, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn zero_seed_handled() {
        let rng = SeededRandom::new(0);
        assert_eq!(rng.seed(), 1);
    }
}
