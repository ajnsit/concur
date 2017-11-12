module.exports = {
    entry: './js-src/index.js',
    output: {
        path: __dirname + '/jsbits',
        filename: 'index.compiled.js',
        // export itself to a global var: "h$concur"
        libraryTarget: "var",
        library: "h$concur"
    }
};
