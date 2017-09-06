#!/bin/bash
browserify jsbits/concur.js | uglifyjs > jsbits/concur.compiled.js
stack build --stack-yaml stack-ghcjs.yaml --no-nix
