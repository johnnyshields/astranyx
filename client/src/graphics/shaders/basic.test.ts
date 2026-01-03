import { describe, it, expect } from 'vitest'
import { VERTEX_SHADER, FRAGMENT_SHADER, GLOW_FRAGMENT } from './basic'

describe('basic shaders', () => {
  describe('VERTEX_SHADER', () => {
    it('is a valid GLSL 300 ES string', () => {
      expect(VERTEX_SHADER).toContain('#version 300 es')
    })

    it('declares required attributes', () => {
      expect(VERTEX_SHADER).toContain('in vec3 aPosition')
      expect(VERTEX_SHADER).toContain('in vec3 aNormal')
    })

    it('declares required uniforms', () => {
      expect(VERTEX_SHADER).toContain('uniform mat4 uProjection')
      expect(VERTEX_SHADER).toContain('uniform mat4 uView')
      expect(VERTEX_SHADER).toContain('uniform mat4 uModel')
      expect(VERTEX_SHADER).toContain('uniform mat3 uNormalMatrix')
      expect(VERTEX_SHADER).toContain('uniform float uTime')
    })

    it('declares required outputs', () => {
      expect(VERTEX_SHADER).toContain('out vec3 vNormal')
      expect(VERTEX_SHADER).toContain('out vec3 vWorldPos')
      expect(VERTEX_SHADER).toContain('out float vTime')
    })

    it('has main function', () => {
      expect(VERTEX_SHADER).toContain('void main()')
    })

    it('computes gl_Position', () => {
      expect(VERTEX_SHADER).toContain('gl_Position')
    })
  })

  describe('FRAGMENT_SHADER', () => {
    it('is a valid GLSL 300 ES string', () => {
      expect(FRAGMENT_SHADER).toContain('#version 300 es')
    })

    it('declares required inputs matching vertex outputs', () => {
      expect(FRAGMENT_SHADER).toContain('in vec3 vNormal')
      expect(FRAGMENT_SHADER).toContain('in vec3 vWorldPos')
      expect(FRAGMENT_SHADER).toContain('in float vTime')
    })

    it('declares required uniforms', () => {
      expect(FRAGMENT_SHADER).toContain('uniform vec4 uColor')
      expect(FRAGMENT_SHADER).toContain('uniform vec3 uCameraPos')
    })

    it('declares output fragment color', () => {
      expect(FRAGMENT_SHADER).toContain('out vec4 fragColor')
    })

    it('implements Blinn-Phong lighting', () => {
      expect(FRAGMENT_SHADER).toContain('diffuse')
      expect(FRAGMENT_SHADER).toContain('specular')
      expect(FRAGMENT_SHADER).toContain('ambient')
    })

    it('implements rim lighting for sci-fi effect', () => {
      expect(FRAGMENT_SHADER).toContain('rim')
    })

    it('has main function', () => {
      expect(FRAGMENT_SHADER).toContain('void main()')
    })
  })

  describe('GLOW_FRAGMENT', () => {
    it('is a valid GLSL 300 ES string', () => {
      expect(GLOW_FRAGMENT).toContain('#version 300 es')
    })

    it('declares texture sampler uniform', () => {
      expect(GLOW_FRAGMENT).toContain('uniform sampler2D uTexture')
    })

    it('declares resolution uniform', () => {
      expect(GLOW_FRAGMENT).toContain('uniform vec2 uResolution')
    })

    it('declares intensity uniform', () => {
      expect(GLOW_FRAGMENT).toContain('uniform float uIntensity')
    })

    it('implements blur for bloom effect', () => {
      expect(GLOW_FRAGMENT).toContain('blur')
      expect(GLOW_FRAGMENT).toContain('texelSize')
    })

    it('has main function', () => {
      expect(GLOW_FRAGMENT).toContain('void main()')
    })
  })

  describe('shader compatibility', () => {
    it('vertex and fragment shader varyings match', () => {
      // vec3 varyings
      const vec3Varyings = ['vNormal', 'vWorldPos']
      for (const varying of vec3Varyings) {
        expect(VERTEX_SHADER).toContain(`out vec3 ${varying}`)
        expect(FRAGMENT_SHADER).toContain(`in vec3 ${varying}`)
      }

      // float varyings
      expect(VERTEX_SHADER).toContain('out float vTime')
      expect(FRAGMENT_SHADER).toContain('in float vTime')
    })
  })
})
