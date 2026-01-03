import { describe, it, expect, vi, beforeEach } from 'vitest'
import { createShader, createProgram } from './shaderUtils'

describe('shaderUtils', () => {
  describe('createShader', () => {
    let mockGl: WebGL2RenderingContext

    beforeEach(() => {
      mockGl = {
        createShader: vi.fn(),
        shaderSource: vi.fn(),
        compileShader: vi.fn(),
        getShaderParameter: vi.fn(),
        getShaderInfoLog: vi.fn(),
        deleteShader: vi.fn(),
        VERTEX_SHADER: 35633,
        FRAGMENT_SHADER: 35632,
        COMPILE_STATUS: 35713,
      } as unknown as WebGL2RenderingContext
    })

    it('creates a shader successfully', () => {
      const mockShader = {} as WebGLShader
      vi.mocked(mockGl.createShader).mockReturnValue(mockShader)
      vi.mocked(mockGl.getShaderParameter).mockReturnValue(true)

      const result = createShader(mockGl, mockGl.VERTEX_SHADER, 'shader source')

      expect(mockGl.createShader).toHaveBeenCalledWith(mockGl.VERTEX_SHADER)
      expect(mockGl.shaderSource).toHaveBeenCalledWith(mockShader, 'shader source')
      expect(mockGl.compileShader).toHaveBeenCalledWith(mockShader)
      expect(result).toBe(mockShader)
    })

    it('throws error when shader creation fails', () => {
      vi.mocked(mockGl.createShader).mockReturnValue(null)

      expect(() => {
        createShader(mockGl, mockGl.VERTEX_SHADER, 'shader source')
      }).toThrow('Failed to create shader')
    })

    it('throws error when shader compilation fails', () => {
      const mockShader = {} as WebGLShader
      vi.mocked(mockGl.createShader).mockReturnValue(mockShader)
      vi.mocked(mockGl.getShaderParameter).mockReturnValue(false)
      vi.mocked(mockGl.getShaderInfoLog).mockReturnValue('Syntax error at line 1')

      expect(() => {
        createShader(mockGl, mockGl.VERTEX_SHADER, 'invalid source')
      }).toThrow('Shader compilation failed: Syntax error at line 1')

      expect(mockGl.deleteShader).toHaveBeenCalledWith(mockShader)
    })
  })

  describe('createProgram', () => {
    let mockGl: WebGL2RenderingContext
    let mockVertexShader: WebGLShader
    let mockFragmentShader: WebGLShader

    beforeEach(() => {
      mockVertexShader = {} as WebGLShader
      mockFragmentShader = {} as WebGLShader

      mockGl = {
        createProgram: vi.fn(),
        attachShader: vi.fn(),
        linkProgram: vi.fn(),
        getProgramParameter: vi.fn(),
        getProgramInfoLog: vi.fn(),
        deleteProgram: vi.fn(),
        deleteShader: vi.fn(),
        LINK_STATUS: 35714,
      } as unknown as WebGL2RenderingContext
    })

    it('creates a program successfully', () => {
      const mockProgram = {} as WebGLProgram
      vi.mocked(mockGl.createProgram).mockReturnValue(mockProgram)
      vi.mocked(mockGl.getProgramParameter).mockReturnValue(true)

      const result = createProgram(mockGl, mockVertexShader, mockFragmentShader)

      expect(mockGl.createProgram).toHaveBeenCalled()
      expect(mockGl.attachShader).toHaveBeenCalledWith(mockProgram, mockVertexShader)
      expect(mockGl.attachShader).toHaveBeenCalledWith(mockProgram, mockFragmentShader)
      expect(mockGl.linkProgram).toHaveBeenCalledWith(mockProgram)
      expect(mockGl.deleteShader).toHaveBeenCalledWith(mockVertexShader)
      expect(mockGl.deleteShader).toHaveBeenCalledWith(mockFragmentShader)
      expect(result).toBe(mockProgram)
    })

    it('throws error when program creation fails', () => {
      vi.mocked(mockGl.createProgram).mockReturnValue(null)

      expect(() => {
        createProgram(mockGl, mockVertexShader, mockFragmentShader)
      }).toThrow('Failed to create program')
    })

    it('throws error when program linking fails', () => {
      const mockProgram = {} as WebGLProgram
      vi.mocked(mockGl.createProgram).mockReturnValue(mockProgram)
      vi.mocked(mockGl.getProgramParameter).mockReturnValue(false)
      vi.mocked(mockGl.getProgramInfoLog).mockReturnValue('Link error: missing main')

      expect(() => {
        createProgram(mockGl, mockVertexShader, mockFragmentShader)
      }).toThrow('Program linking failed: Link error: missing main')

      expect(mockGl.deleteProgram).toHaveBeenCalledWith(mockProgram)
    })
  })
})
