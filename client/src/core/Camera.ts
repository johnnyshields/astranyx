import { Matrix4 } from '../math/Matrix4.ts'

export interface PlayBounds {
  leftX: number
  rightX: number
  getTopY: (x: number) => number
  getBottomY: (x: number) => number
}

/**
 * Camera class for 2.5D Einhänder-style view.
 * Manages view and projection matrices with perspective tilt.
 */
export class Camera {
  private viewMatrix: Matrix4
  private projectionMatrix: Matrix4

  private position: { x: number; y: number; z: number } = { x: 0, y: 0, z: 900 }
  private target: { x: number; y: number; z: number } = { x: 0, y: 0, z: 0 }
  private up: { x: number; y: number; z: number } = { x: 0, y: 1, z: 0 }

  private distance: number = 900
  private tiltAngle: number = 20 * (Math.PI / 180) // 20 degrees
  private fov: number = 45 * (Math.PI / 180)
  private aspect: number = 5 / 3
  private near: number = 10
  private far: number = 2000

  constructor() {
    this.viewMatrix = Matrix4.identity()
    this.projectionMatrix = Matrix4.identity()
    this.updateMatrices()
  }

  /**
   * Get the view matrix
   */
  getViewMatrix(): Matrix4 {
    return this.viewMatrix
  }

  /**
   * Get the projection matrix
   */
  getProjectionMatrix(): Matrix4 {
    return this.projectionMatrix
  }

  /**
   * Get the view-projection matrix (combined)
   */
  getViewProjectionMatrix(): Matrix4 {
    return this.projectionMatrix.multiplied(this.viewMatrix)
  }

  /**
   * Get camera position
   */
  getPosition(): { x: number; y: number; z: number } {
    return { ...this.position }
  }

  /**
   * Get camera distance from origin
   */
  getDistance(): number {
    return this.distance
  }

  /**
   * Set camera distance
   */
  setDistance(distance: number): void {
    this.distance = distance
    this.updateMatrices()
  }

  /**
   * Get camera tilt angle in radians
   */
  getTiltAngle(): number {
    return this.tiltAngle
  }

  /**
   * Set camera tilt angle in radians
   */
  setTiltAngle(angle: number): void {
    this.tiltAngle = angle
    this.updateMatrices()
  }

  /**
   * Set camera tilt angle in degrees
   */
  setTiltAngleDegrees(degrees: number): void {
    this.setTiltAngle(degrees * (Math.PI / 180))
  }

  /**
   * Get field of view in radians
   */
  getFov(): number {
    return this.fov
  }

  /**
   * Set field of view in radians
   */
  setFov(fov: number): void {
    this.fov = fov
    this.updateMatrices()
  }

  /**
   * Set field of view in degrees
   */
  setFovDegrees(degrees: number): void {
    this.setFov(degrees * (Math.PI / 180))
  }

  /**
   * Get aspect ratio
   */
  getAspect(): number {
    return this.aspect
  }

  /**
   * Set aspect ratio
   */
  setAspect(aspect: number): void {
    this.aspect = aspect
    this.updateMatrices()
  }

  /**
   * Set near/far clipping planes
   */
  setClipPlanes(near: number, far: number): void {
    this.near = near
    this.far = far
    this.updateMatrices()
  }

  /**
   * Update all matrices based on current settings
   */
  updateMatrices(): void {
    // Calculate camera position with tilt
    // Camera is in front (positive Z) and slightly to the LEFT for Einhänder-style tilt
    this.position.x = -this.distance * Math.sin(this.tiltAngle)
    this.position.y = 0
    this.position.z = this.distance * Math.cos(this.tiltAngle)

    // Update view matrix
    this.viewMatrix.setLookAt(
      this.position.x,
      this.position.y,
      this.position.z,
      this.target.x,
      this.target.y,
      this.target.z,
      this.up.x,
      this.up.y,
      this.up.z
    )

    // Update projection matrix
    this.projectionMatrix.setPerspective(this.fov, this.aspect, this.near, this.far)
  }

  /**
   * Set orthographic projection
   */
  setOrthographic(left: number, right: number, bottom: number, top: number): void {
    this.projectionMatrix.setOrthographic(left, right, bottom, top, this.near, this.far)
  }

  /**
   * Restore perspective projection
   */
  setPerspective(): void {
    this.projectionMatrix.setPerspective(this.fov, this.aspect, this.near, this.far)
  }

  /**
   * Project a world point to normalized device coordinates
   */
  worldToNDC(worldX: number, worldY: number, worldZ: number): { x: number; y: number; z: number } {
    const vp = this.getViewProjectionMatrix()
    return vp.transformPoint(worldX, worldY, worldZ)
  }

  /**
   * Unproject NDC point to world coordinates at z=0 plane
   */
  ndcToWorld(ndcX: number, ndcY: number): { x: number; y: number } {
    const invVP = this.getViewProjectionMatrix().inverted()

    // Create ray from near and far planes
    const nearPoint = invVP.transformPoint(ndcX, ndcY, -1)
    const farPoint = invVP.transformPoint(ndcX, ndcY, 1)

    // Find intersection with z=0 plane
    const dz = farPoint.z - nearPoint.z
    if (Math.abs(dz) < 0.0001) {
      return { x: nearPoint.x, y: nearPoint.y }
    }

    const t = -nearPoint.z / dz
    return {
      x: nearPoint.x + t * (farPoint.x - nearPoint.x),
      y: nearPoint.y + t * (farPoint.y - nearPoint.y),
    }
  }

  /**
   * Calculate the world-space play bounds visible in the viewport.
   * Returns bounds at the z=0 plane accounting for perspective and tilt.
   */
  getPlayBounds(): PlayBounds {
    const invVP = this.getViewProjectionMatrix().inverted()

    // Unproject viewport corners to z=0 plane
    const corners = [
      this.unprojectToZ0(invVP, -1, -1), // bottom-left
      this.unprojectToZ0(invVP, 1, -1), // bottom-right
      this.unprojectToZ0(invVP, 1, 1), // top-right
      this.unprojectToZ0(invVP, -1, 1), // top-left
    ]

    const leftX = (corners[0]!.x + corners[3]!.x) / 2
    const rightX = (corners[1]!.x + corners[2]!.x) / 2 - 100 // Buffer on right

    const leftBottomY = corners[0]!.y
    const leftTopY = corners[3]!.y
    const rightBottomY = corners[1]!.y
    const rightTopY = corners[2]!.y

    return {
      leftX,
      rightX,
      getTopY: (x: number) => {
        const t = (x - leftX) / (rightX - leftX)
        return leftTopY + t * (rightTopY - leftTopY)
      },
      getBottomY: (x: number) => {
        const t = (x - leftX) / (rightX - leftX)
        return leftBottomY + t * (rightBottomY - leftBottomY)
      },
    }
  }

  private unprojectToZ0(invVP: Matrix4, ndcX: number, ndcY: number): { x: number; y: number } {
    const nearPoint = invVP.transformPoint(ndcX, ndcY, -1)
    const farPoint = invVP.transformPoint(ndcX, ndcY, 1)

    const dz = farPoint.z - nearPoint.z
    if (Math.abs(dz) < 0.0001) {
      return { x: nearPoint.x, y: nearPoint.y }
    }

    const t = -nearPoint.z / dz
    return {
      x: nearPoint.x + t * (farPoint.x - nearPoint.x),
      y: nearPoint.y + t * (farPoint.y - nearPoint.y),
    }
  }

  /**
   * Clone this camera
   */
  clone(): Camera {
    const camera = new Camera()
    camera.distance = this.distance
    camera.tiltAngle = this.tiltAngle
    camera.fov = this.fov
    camera.aspect = this.aspect
    camera.near = this.near
    camera.far = this.far
    camera.updateMatrices()
    return camera
  }
}
