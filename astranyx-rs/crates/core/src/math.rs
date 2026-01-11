//! Deterministic math functions for cross-platform consistency.
//!
//! Hardware floating point implementations of trig functions can differ
//! between architectures (x86 vs ARM vs WASM). This module provides
//! software implementations that produce identical results everywhere.
//!
//! Critical for P2P lockstep networking where all clients must compute
//! identical results.

use std::f32::consts::PI;

/// Deterministic atan for a single value.
/// Uses a polynomial from Abramowitz & Stegun (accurate to ~0.0005 rad).
#[inline]
fn atan_det(x: f32) -> f32 {
    let sign = x.signum();
    let x = x.abs();

    // For |x| > 1, use identity: atan(x) = PI/2 - atan(1/x)
    let (z, base) = if x > 1.0 {
        (1.0 / x, PI / 2.0)
    } else {
        (x, 0.0)
    };

    // Polynomial approximation using Horner's form for numerical stability
    let z2 = z * z;

    // atan(z) for |z| <= 1 using Chebyshev-derived coefficients
    // These are more accurate than Taylor coefficients
    let a1 = -0.333331346;
    let a2 = 0.199900893;
    let a3 = -0.142006844;
    let a4 = 0.106347479;
    let a5 = -0.074890330;
    let a6 = 0.042972115;
    let a7 = -0.016045005;

    let result = z * (1.0 + z2 * (a1 + z2 * (a2 + z2 * (a3 + z2 * (a4 + z2 * (a5 + z2 * (a6 + z2 * a7)))))));

    let angle = if x > 1.0 { base - result } else { result };
    sign * angle
}

/// Deterministic atan2.
/// Returns angle in radians in range [-PI, PI].
///
/// Uses a polynomial approximation for cross-platform consistency.
/// Maximum error: ~0.0005 radians (~0.03 degrees).
#[inline]
pub fn atan2_det(y: f32, x: f32) -> f32 {
    // Handle special cases
    if x == 0.0 && y == 0.0 {
        return 0.0;
    }
    if x == 0.0 {
        return if y > 0.0 { PI / 2.0 } else { -PI / 2.0 };
    }
    if y == 0.0 {
        return if x > 0.0 { 0.0 } else { PI };
    }

    // Compute atan(y/x)
    let atan_val = atan_det(y / x);

    // Adjust for quadrant
    if x > 0.0 {
        atan_val
    } else if y >= 0.0 {
        atan_val + PI
    } else {
        atan_val - PI
    }
}

/// Deterministic sine using polynomial approximation.
/// Input in radians, returns value in [-1, 1].
///
/// Uses Bhaskara I's approximation, accurate to ~0.001.
#[inline]
pub fn sin_det(x: f32) -> f32 {
    // Normalize to [0, 2π]
    let x = normalize_angle(x);

    // Use symmetry to map to [0, π]
    let (x, sign) = if x > PI { (x - PI, -1.0) } else { (x, 1.0) };

    // Bhaskara I's sine approximation: sin(x) ≈ 16x(π-x) / (5π² - 4x(π-x))
    // Valid for x in [0, π], very accurate
    let numerator = 16.0 * x * (PI - x);
    let denominator = 5.0 * PI * PI - 4.0 * x * (PI - x);

    sign * numerator / denominator
}

/// Deterministic cosine using polynomial approximation.
/// Input in radians, returns value in [-1, 1].
#[inline]
pub fn cos_det(x: f32) -> f32 {
    // cos(x) = sin(x + π/2)
    sin_det(x + PI / 2.0)
}

/// Normalize angle to [0, 2π].
#[inline]
fn normalize_angle(mut x: f32) -> f32 {
    const TWO_PI: f32 = 2.0 * PI;

    // Fast modulo for common cases
    while x < 0.0 {
        x += TWO_PI;
    }
    while x >= TWO_PI {
        x -= TWO_PI;
    }
    x
}

/// Normalize angle difference to [-π, π].
#[inline]
pub fn normalize_angle_diff(mut angle: f32) -> f32 {
    while angle > PI {
        angle -= 2.0 * PI;
    }
    while angle < -PI {
        angle += 2.0 * PI;
    }
    angle
}

/// Deterministic square root using Newton-Raphson iteration.
/// Produces identical results across all platforms.
#[inline]
pub fn sqrt_det(x: f32) -> f32 {
    if x <= 0.0 {
        return 0.0;
    }

    // Initial guess using bit manipulation (fast inverse sqrt trick)
    let mut guess = x;
    let i = guess.to_bits();
    let i = 0x5f375a86 - (i >> 1); // Magic number for sqrt
    guess = f32::from_bits(i);
    guess = 1.0 / guess; // Convert from inverse sqrt to sqrt

    // Newton-Raphson iterations for precision
    // x_{n+1} = 0.5 * (x_n + S/x_n)
    guess = 0.5 * (guess + x / guess);
    guess = 0.5 * (guess + x / guess);
    guess = 0.5 * (guess + x / guess); // 3 iterations is enough for f32

    guess
}

/// Deterministic vector length using deterministic sqrt.
#[inline]
pub fn length_det(x: f32, y: f32) -> f32 {
    sqrt_det(x * x + y * y)
}

/// Deterministic 3D vector length.
#[inline]
pub fn length3_det(x: f32, y: f32, z: f32) -> f32 {
    sqrt_det(x * x + y * y + z * z)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_atan2_quadrants() {
        // Test all four quadrants
        let eps = 0.01;

        // Q1: +x, +y -> 0 to π/2
        let a1 = atan2_det(1.0, 1.0);
        assert!((a1 - PI / 4.0).abs() < eps, "Q1: got {}", a1);

        // Q2: -x, +y -> π/2 to π
        let a2 = atan2_det(1.0, -1.0);
        assert!((a2 - 3.0 * PI / 4.0).abs() < eps, "Q2: got {}", a2);

        // Q3: -x, -y -> -π to -π/2
        let a3 = atan2_det(-1.0, -1.0);
        assert!((a3 - (-3.0 * PI / 4.0)).abs() < eps, "Q3: got {}", a3);

        // Q4: +x, -y -> -π/2 to 0
        let a4 = atan2_det(-1.0, 1.0);
        assert!((a4 - (-PI / 4.0)).abs() < eps, "Q4: got {}", a4);
    }

    #[test]
    fn test_atan2_axes() {
        let eps = 0.01;

        assert!(atan2_det(0.0, 1.0).abs() < eps); // +x axis -> 0
        assert!((atan2_det(1.0, 0.0) - PI / 2.0).abs() < eps); // +y axis -> π/2
        assert!((atan2_det(0.0, -1.0).abs() - PI).abs() < eps); // -x axis -> ±π
        assert!((atan2_det(-1.0, 0.0) - (-PI / 2.0)).abs() < eps); // -y axis -> -π/2
    }

    #[test]
    fn test_sin_cos_det() {
        let eps = 0.01;

        // Test key angles
        assert!(sin_det(0.0).abs() < eps);
        assert!((sin_det(PI / 2.0) - 1.0).abs() < eps);
        assert!(sin_det(PI).abs() < eps);
        assert!((sin_det(3.0 * PI / 2.0) - (-1.0)).abs() < eps);

        assert!((cos_det(0.0) - 1.0).abs() < eps);
        assert!(cos_det(PI / 2.0).abs() < eps);
        assert!((cos_det(PI) - (-1.0)).abs() < eps);
        assert!(cos_det(3.0 * PI / 2.0).abs() < eps);
    }

    #[test]
    fn test_sqrt_det() {
        let eps = 0.001;

        assert!((sqrt_det(4.0) - 2.0).abs() < eps);
        assert!((sqrt_det(9.0) - 3.0).abs() < eps);
        assert!((sqrt_det(2.0) - 1.414).abs() < eps);
        assert!((sqrt_det(0.25) - 0.5).abs() < eps);
        assert_eq!(sqrt_det(0.0), 0.0);
    }

    #[test]
    fn test_length_det() {
        let eps = 0.001;

        // 3-4-5 triangle
        assert!((length_det(3.0, 4.0) - 5.0).abs() < eps);

        // Unit vector
        assert!((length_det(1.0, 0.0) - 1.0).abs() < eps);

        // Diagonal
        let sqrt2 = sqrt_det(2.0);
        assert!((length_det(1.0, 1.0) - sqrt2).abs() < eps);
    }

    #[test]
    fn test_determinism() {
        // Run the same calculations multiple times to verify determinism
        let results1: Vec<f32> = (0..100)
            .map(|i| {
                let x = i as f32 * 0.1;
                atan2_det(sin_det(x), cos_det(x))
            })
            .collect();

        let results2: Vec<f32> = (0..100)
            .map(|i| {
                let x = i as f32 * 0.1;
                atan2_det(sin_det(x), cos_det(x))
            })
            .collect();

        assert_eq!(results1, results2, "Results should be identical");
    }
}
