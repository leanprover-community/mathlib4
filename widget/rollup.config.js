import glob from 'glob';
import { nodeResolve } from '@rollup/plugin-node-resolve'
import typescript from '@rollup/plugin-typescript';
import commonjs from '@rollup/plugin-commonjs';
import replace from '@rollup/plugin-replace';
import terser from '@rollup/plugin-terser';
import css from "rollup-plugin-import-css";

/** @type {(_: any) => import('rollup').RollupOptions} */
export default cliArgs => {
    const tsxName = cliArgs.tsxName;
    if (tsxName !== undefined)
        // We delete the custom argument so that Rollup does not try to process it and complain.
        delete cliArgs.tsxName;

    const inputs = tsxName ?
        [ `src/${tsxName}.tsx` ] :
        glob.sync('src/**/*.tsx')

    const configForInput = fname => ({
    input: fname,
    output: {
        dir: '../build/js',
        format: 'es',
        // Hax: apparently setting `global` makes some CommonJS modules work ¯\_(ツ)_/¯
        intro: 'const global = window;'
    },
    external: [
        'react',
        'react-dom',
        'react/jsx-runtime',
        '@leanprover/infoview',
    ],
    plugins: [
        typescript({
            tsconfig: './tsconfig.json',
            outputToFilesystem: false,
        }),
        nodeResolve({
            browser: true
        }),
        replace({
            'typeof window': JSON.stringify('object'),
            'process.env.NODE_ENV': JSON.stringify(process.env.NODE_ENV),
            preventAssignment: true // TODO delete when `true` becomes the default
        }),
        commonjs({
            // In some cases the common.js plugin will hoist dynamic `require` calls for Node.js
            // modules which are not ever actually called into a global `import` which we cannot
            // resolve since we are running in a browser. So block all these from being hoisted.
            // Note: one alternative, https://github.com/FredKSchott/rollup-plugin-polyfill-node
            // does not seem to work.
            ignore: [
                'process', 'events', 'stream', 'util', 'path', 'buffer', 'querystring', 'url',
                'string_decoder', 'punycode', 'http', 'https', 'os', 'assert', 'constants',
                'timers', 'console', 'vm', 'zlib', 'tty', 'domain', 'dns', 'dgram', 'child_process',
                'cluster', 'module', 'net', 'readline', 'repl', 'tls', 'fs', 'crypto', 'perf_hooks',
            ],
        }),
        terser(),
        css()
    ],
    })

    // For why we must return an array of configs rather than use an array in `input`, see
    // https://github.com/rollup/rollup/issues/2756. This is pretty suboptimal as every build
    // rechecks all TS files, so the process is quadratic.
    return inputs.map(configForInput)
}
