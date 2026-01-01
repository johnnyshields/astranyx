/**
 * Environment Detection Utilities
 *
 * For Vite-built code. Uses import.meta.env which is baked in at build time.
 *
 * Environments are distinct deployment contexts (mutually exclusive):
 * - development: Local development (Vite dev server)
 * - test: Automated test runner (Vitest)
 * - preview: Production build running locally (bun run preview)
 * - staging: Prod build on staging server
 * - production: True production
 */

export type Environment = 'development' | 'test' | 'preview' | 'staging' | 'production'

/**
 * Check if running in Vite development mode (not a production build).
 * This is about the BUILD, not the deployment environment.
 */
export function isDevBuild(): boolean {
  return import.meta.env?.DEV === true
}

/**
 * Check if running a production build.
 * This is about the BUILD, not the deployment environment.
 */
export function isProdBuild(): boolean {
  return import.meta.env?.PROD === true
}

/**
 * Get the current environment name.
 * Environments are mutually exclusive.
 */
export function getEnvironment(): Environment {
  // Test environment (checked first - highest priority)
  if (
    typeof process !== 'undefined' &&
    (process.env.NODE_ENV === 'test' || process.env.VITEST === 'true')
  ) {
    return 'test'
  }

  // Explicit environment variable (VITE_ENV)
  const viteEnv = import.meta.env?.VITE_ENV

  // Dev build can only be development
  if (isDevBuild()) {
    return 'development'
  }

  // Prod build: check VITE_ENV, default to preview
  if (isProdBuild()) {
    if (viteEnv === 'staging') return 'staging'
    if (viteEnv === 'production') return 'production'
    return 'preview'
  }

  // Fallback for ambiguous state
  return 'development'
}

// =============================================================================
// Environment checks
// =============================================================================

/** Check if running in test environment (Vitest). */
export function isTest(): boolean {
  return getEnvironment() === 'test'
}

/** Check if running in development environment (Vite dev server). */
export function isDevelopment(): boolean {
  return getEnvironment() === 'development'
}

/** Check if running in preview environment (production build running locally). */
export function isPreview(): boolean {
  return getEnvironment() === 'preview'
}

/** Check if running in staging environment. */
export function isStaging(): boolean {
  return getEnvironment() === 'staging'
}

/** Check if running in true production environment. */
export function isProduction(): boolean {
  return getEnvironment() === 'production'
}

// =============================================================================
// Composite checks
// =============================================================================

/** Check if running in a local environment (development, test, or preview). */
export function isLocal(): boolean {
  const env = getEnvironment()
  return env === 'development' || env === 'test' || env === 'preview'
}

/** Check if running in a deployed environment (staging or production). */
export function isRemote(): boolean {
  return !isLocal()
}
