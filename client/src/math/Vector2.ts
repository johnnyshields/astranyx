/**
 * 2D Vector class for game math operations.
 * Supports both mutable and immutable operations.
 */
export class Vector2 {
  constructor(
    public x: number = 0,
    public y: number = 0
  ) {}

  /**
   * Create a vector from angle (radians) and magnitude
   */
  static fromAngle(angle: number, magnitude = 1): Vector2 {
    return new Vector2(Math.cos(angle) * magnitude, Math.sin(angle) * magnitude)
  }

  /**
   * Create a zero vector
   */
  static zero(): Vector2 {
    return new Vector2(0, 0)
  }

  /**
   * Create a unit vector pointing right (positive X)
   */
  static right(): Vector2 {
    return new Vector2(1, 0)
  }

  /**
   * Create a unit vector pointing up (positive Y)
   */
  static up(): Vector2 {
    return new Vector2(0, 1)
  }

  /**
   * Create a copy of this vector
   */
  clone(): Vector2 {
    return new Vector2(this.x, this.y)
  }

  /**
   * Set both components
   */
  set(x: number, y: number): this {
    this.x = x
    this.y = y
    return this
  }

  /**
   * Copy values from another vector
   */
  copy(other: Vector2): this {
    this.x = other.x
    this.y = other.y
    return this
  }

  /**
   * Add another vector (mutates this)
   */
  add(other: Vector2): this {
    this.x += other.x
    this.y += other.y
    return this
  }

  /**
   * Add another vector (returns new vector)
   */
  plus(other: Vector2): Vector2 {
    return new Vector2(this.x + other.x, this.y + other.y)
  }

  /**
   * Subtract another vector (mutates this)
   */
  sub(other: Vector2): this {
    this.x -= other.x
    this.y -= other.y
    return this
  }

  /**
   * Subtract another vector (returns new vector)
   */
  minus(other: Vector2): Vector2 {
    return new Vector2(this.x - other.x, this.y - other.y)
  }

  /**
   * Multiply by scalar (mutates this)
   */
  scale(scalar: number): this {
    this.x *= scalar
    this.y *= scalar
    return this
  }

  /**
   * Multiply by scalar (returns new vector)
   */
  scaled(scalar: number): Vector2 {
    return new Vector2(this.x * scalar, this.y * scalar)
  }

  /**
   * Component-wise multiplication (mutates this)
   */
  multiply(other: Vector2): this {
    this.x *= other.x
    this.y *= other.y
    return this
  }

  /**
   * Component-wise multiplication (returns new vector)
   */
  multiplied(other: Vector2): Vector2 {
    return new Vector2(this.x * other.x, this.y * other.y)
  }

  /**
   * Divide by scalar (mutates this)
   */
  divideScalar(scalar: number): this {
    if (scalar !== 0) {
      this.x /= scalar
      this.y /= scalar
    }
    return this
  }

  /**
   * Negate this vector (mutates this)
   */
  negate(): this {
    this.x = -this.x
    this.y = -this.y
    return this
  }

  /**
   * Return negated vector (returns new vector)
   */
  negated(): Vector2 {
    return new Vector2(-this.x, -this.y)
  }

  /**
   * Get the squared length (magnitude squared) - faster than length()
   */
  lengthSquared(): number {
    return this.x * this.x + this.y * this.y
  }

  /**
   * Get the length (magnitude) of this vector
   */
  length(): number {
    return Math.sqrt(this.lengthSquared())
  }

  /**
   * Normalize this vector to unit length (mutates this)
   */
  normalize(): this {
    const len = this.length()
    if (len > 0) {
      this.x /= len
      this.y /= len
    }
    return this
  }

  /**
   * Return normalized vector (returns new vector)
   */
  normalized(): Vector2 {
    const len = this.length()
    if (len === 0) return new Vector2(0, 0)
    return new Vector2(this.x / len, this.y / len)
  }

  /**
   * Set the length of this vector (mutates this)
   */
  setLength(newLength: number): this {
    this.normalize().scale(newLength)
    return this
  }

  /**
   * Limit the length of this vector (mutates this)
   */
  limit(maxLength: number): this {
    const lenSq = this.lengthSquared()
    if (lenSq > maxLength * maxLength) {
      this.divideScalar(Math.sqrt(lenSq)).scale(maxLength)
    }
    return this
  }

  /**
   * Dot product with another vector
   */
  dot(other: Vector2): number {
    return this.x * other.x + this.y * other.y
  }

  /**
   * Cross product (returns scalar - Z component of 3D cross product)
   */
  cross(other: Vector2): number {
    return this.x * other.y - this.y * other.x
  }

  /**
   * Get the angle of this vector in radians
   */
  angle(): number {
    return Math.atan2(this.y, this.x)
  }

  /**
   * Get the angle between this vector and another in radians
   */
  angleTo(other: Vector2): number {
    return Math.atan2(this.cross(other), this.dot(other))
  }

  /**
   * Rotate this vector by angle in radians (mutates this)
   */
  rotate(angle: number): this {
    const cos = Math.cos(angle)
    const sin = Math.sin(angle)
    const x = this.x * cos - this.y * sin
    const y = this.x * sin + this.y * cos
    this.x = x
    this.y = y
    return this
  }

  /**
   * Return rotated vector (returns new vector)
   */
  rotated(angle: number): Vector2 {
    const cos = Math.cos(angle)
    const sin = Math.sin(angle)
    return new Vector2(this.x * cos - this.y * sin, this.x * sin + this.y * cos)
  }

  /**
   * Get perpendicular vector (rotated 90 degrees counter-clockwise)
   */
  perpendicular(): Vector2 {
    return new Vector2(-this.y, this.x)
  }

  /**
   * Distance to another vector
   */
  distanceTo(other: Vector2): number {
    const dx = other.x - this.x
    const dy = other.y - this.y
    return Math.sqrt(dx * dx + dy * dy)
  }

  /**
   * Squared distance to another vector (faster than distanceTo)
   */
  distanceSquaredTo(other: Vector2): number {
    const dx = other.x - this.x
    const dy = other.y - this.y
    return dx * dx + dy * dy
  }

  /**
   * Linear interpolation to another vector
   */
  lerp(other: Vector2, t: number): Vector2 {
    return new Vector2(this.x + (other.x - this.x) * t, this.y + (other.y - this.y) * t)
  }

  /**
   * Linear interpolation (mutates this)
   */
  lerpTo(other: Vector2, t: number): this {
    this.x += (other.x - this.x) * t
    this.y += (other.y - this.y) * t
    return this
  }

  /**
   * Reflect this vector off a surface with given normal
   */
  reflect(normal: Vector2): Vector2 {
    const d = 2 * this.dot(normal)
    return new Vector2(this.x - d * normal.x, this.y - d * normal.y)
  }

  /**
   * Check if this vector equals another (with optional epsilon for floating point comparison)
   */
  equals(other: Vector2, epsilon = 0): boolean {
    if (epsilon === 0) {
      return this.x === other.x && this.y === other.y
    }
    return Math.abs(this.x - other.x) <= epsilon && Math.abs(this.y - other.y) <= epsilon
  }

  /**
   * Check if this is a zero vector
   */
  isZero(): boolean {
    return this.x === 0 && this.y === 0
  }

  /**
   * Convert to array [x, y]
   */
  toArray(): [number, number] {
    return [this.x, this.y]
  }

  /**
   * Create from array [x, y]
   */
  static fromArray(arr: [number, number]): Vector2 {
    return new Vector2(arr[0], arr[1])
  }

  /**
   * String representation
   */
  toString(): string {
    return `Vector2(${this.x}, ${this.y})`
  }
}
