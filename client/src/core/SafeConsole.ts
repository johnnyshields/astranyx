/**
 * SafeConsole - Development-only logging
 *
 * In production builds, all log/warn/error calls are no-ops.
 * In development, they pass through to console.
 *
 * Use this for verbose debugging output that should be
 * stripped in production for performance.
 */

const isDev = import.meta.env.DEV

/**
 * Log message (dev only)
 */
export function log(...args: unknown[]): void {
  if (isDev) {
    console.log(...args)
  }
}

/**
 * Warning message (dev only)
 */
export function warn(...args: unknown[]): void {
  if (isDev) {
    console.warn(...args)
  }
}

/**
 * Error message (always logs, even in prod - errors should be visible)
 */
export function error(...args: unknown[]): void {
  console.error(...args)
}

/**
 * Info message (dev only)
 */
export function info(...args: unknown[]): void {
  if (isDev) {
    console.info(...args)
  }
}

/**
 * Debug message (dev only)
 */
export function debug(...args: unknown[]): void {
  if (isDev) {
    console.debug(...args)
  }
}

/**
 * Debug group (dev only)
 */
export function group(label: string): void {
  if (isDev) {
    console.group(label)
  }
}

/**
 * Debug group end (dev only)
 */
export function groupEnd(): void {
  if (isDev) {
    console.groupEnd()
  }
}

export const SafeConsole = {
  log,
  warn,
  error,
  info,
  debug,
  group,
  groupEnd,
}
