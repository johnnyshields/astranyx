import js from '@eslint/js'
import globals from 'globals'
import tseslint from 'typescript-eslint'

export default tseslint.config(
  {
    ignores: ['dist/**', '*.lock', 'bun.lock', 'package-lock.json', 'node_modules/**'],
  },
  js.configs.recommended,
  ...tseslint.configs.recommended,
  {
    files: ['**/*.{ts,tsx}'],
    rules: {
      '@typescript-eslint/no-unused-vars': [
        'error',
        {
          argsIgnorePattern: '^_',
          varsIgnorePattern: '^_',
          caughtErrorsIgnorePattern: '^_',
        },
      ],
    },
    languageOptions: {
      ecmaVersion: 2020,
      globals: globals.browser,
    },
  },
  // Ban console.log/error/warn/etc in src/ - use SafeConsole instead
  {
    files: ['src/**/*.ts'],
    ignores: ['**/*.test.ts', 'src/core/SafeConsole.ts'],
    rules: {
      'no-console': 'error',
    },
  },
)
