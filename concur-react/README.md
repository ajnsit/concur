# Concur - React backend

To build the example files run the following build script (requires Stack):

```
$ ./scripts/build.sh
```

If you get a failed build due to Alex not being found on the path, do the following before re-running the script (your specific path should be in your terminal output):

```
$ export PATH=~/.stack/programs/<architecture>/<ghcjs-version>/bin:$PATH
```

After a successful build you can open the example located at `.stack-work/dist/<arch>/<cabal-version>/build/<examplename>/<examplename>.jsexe/index.html` in your browser.
