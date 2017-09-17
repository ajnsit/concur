module.exports = {
    entry: './js-src/index.js',
    output: {
        path: __dirname + '/jsbits',
        filename: 'index.compiled.js',
        // export itself to a global var: "h$ffi"
        libraryTarget: "var",
        library: "h$ffi"
    },
    externals: {
        // Load React deps from the concur-react library
        "react": "h$concur.React",
        "react-dom": "h$concur.ReactDOM"
    }
};
