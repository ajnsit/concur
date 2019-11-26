<h1 align="center">
    Concur
</h1>
<p align="center">
   <img src="docs/logo.png" height="100">
</p>
<p align="center">
  <a href="https://gitter.im/concurhaskell" rel="nofollow">
      <img src="https://camo.githubusercontent.com/9fb4e2dde684214e7454d930a369f97190d1ecf2/68747470733a2f2f696d672e736869656c64732e696f2f62616467652f6769747465722d6a6f696e253230636861742532302545322538362541332d626c75652e737667" alt="Join the chat at https://gitter.im/concurhaskell" data-canonical-src="https://img.shields.io/badge/gitter-join%20chat%20%E2%86%A3-blue.svg" style="max-width:100%;">
   </a>
   <a href="https://www.reddit.com/r/concurhaskell/" rel="nofollow">
      <img src="https://img.shields.io/badge/reddit-join%20the%20discussion%20%E2%86%A3-1158c2.svg" alt="Join the chat at https://gitter.im/concurhaskell" style="max-width:100%;">
   </a>
</p>

A brand new client side Web UI framework for Haskell that explores an entirely new paradigm. It does not follow FRP (think Reflex or Reactive Banana), or Elm architecture, but aims to combine the best parts of both.

## Documentation

Work in progress tutorials are published in the [Concur Documentation site](https://github.com/ajnsit/concur-documentation/blob/master/README.md)

## Installation

It has three backends -

1. [React](https://github.com/facebook/react) based, called [concur-react](concur-react). You can use the [Concur-React Quickstart Template](https://github.com/concurhaskell/concur-react-starter) to quickly get started.

    An example of using Native React Widgets is here - [Drag Drop Sortable List Widget (React)](https://github.com/concurhaskell/concur-react-sortable-tree/blob/master/src/Main.hs) - [Demo](https://ajnsit.github.io/concur/examples/sortable-tree-example.jsexe/index.html) - Demonstrates Concur binding to [React-Sortable-Tree](https://github.com/fritz-c/react-sortable-tree).

2. [Virtual-Dom](https://github.com/Matt-Esch/virtual-dom) based, called [concur-vdom](concur-vdom). (**Bitrotten**). You can use the [Concur-Vdom Quickstart Template](https://github.com/concurhaskell/concur-vdom-starter) to quickly get started.

3. [Replica](https://github.com/pkamenarsky/replica) (i.e. remote virtual-dom) based, called [concur-replica](https://github.com/pkamenarsky/concur-replica). Created and maintained by [pkamenarsky](https://github.com/pkamenarsky). Head to its [project page](https://github.com/pkamenarsky/concur-replica) for more information.

## Performance

Access some performance benchmarks here - https://ajnsit.github.io/concur-benchmarks/

## Ports to other languages

Concur's model translates well to other platforms.

1. [Concur for Purescript](https://github.com/ajnsit/purescript-concur) - An official port to Purescript which is well maintained.
2. [Concur for Javascript](https://github.com/ajnsit/concur-js) - An official but experimental port to Javascript.
3. [Concur for Python](https://github.com/potocpav/python-concur) - An unofficial and experimental port to Python. Uses ImgUI for graphics. Created and Maintained by [potocpav](https://github.com/potocpav).

## Examples

1. [Click Counting Example](https://github.com/ajnsit/concur/blob/master/concur-vdom/examples/ClickCounter.hs) - [Demo](https://ajnsit.github.io/concur/examples/clickCounter.jsexe/index.html) - Count total number of clicks on the page, with a button that increments the click count by 10, and also autoincrement clicks every second.
2. [TodoMVC Example](https://github.com/ajnsit/concur/blob/master/concur-vdom/examples/Todos.hs) - [Demo](https://ajnsit.github.io/concur/examples/todos.jsexe/index.html) - The canonical TodoMVC example, with views modeled after the one in Elm.
3. [Mario Example](https://github.com/ajnsit/concur/blob/master/concur-vdom/examples/Mario.hs) - [Demo](https://ajnsit.github.io/concur/examples/mario.jsexe/index.html) - Port of the Mario example from Elm.
4. [High/Low Game (Virtual-dom)](https://github.com/ajnsit/concur/blob/master/concur-vdom/examples/HiLo.hs) - [Demo](https://ajnsit.github.io/concur/examples/hilo.jsexe/index.html) - An extremely simple number guessing game in 15 lines of code.
5. [High/Low Game (React)](https://github.com/ajnsit/concur/blob/master/concur-react/examples/HiLo.hs) - [Demo](https://ajnsit.github.io/concur/examples/concur-react-hilo.jsexe/index.html) - The same HiLo game, using the React backend.
6. [Kirby Super Star Ultra Splits Timer GUI Challange](https://github.com/ajnsit/concur/blob/master/concur-vdom/examples/KirbySuperStarUltra.hs) - [Demo](https://ajnsit.github.io/concur/examples/kssu.jsexe/index.html) - Concur implementation of the [KSSU Splits Timer GUI Challenge](https://gist.github.com/lexi-lambda/701f1f1282401059f13a4220e8178ba4). Shows a moderately complex UI that's not a todolist!
7. [Menu Widget (React)](https://github.com/ajnsit/concur/blob/master/concur-react/examples/Menu.hs) - [Demo](https://ajnsit.github.io/concur/examples/concur-react-menu.jsexe/index.html) - Builds a generic menu widget in 10 lines of code.
8. [Drag Drop Sortable List Widget (React)](https://github.com/concurhaskell/concur-react-sortable-tree/blob/master/src/Main.hs) - [Demo](https://ajnsit.github.io/concur/examples/sortable-tree-example.jsexe/index.html) - Demonstrates Concur binding to [React-Sortable-Tree](https://github.com/fritz-c/react-sortable-tree). A good example of reusing existing React components in Concur.
9. [Your first 8 Concur Pipes Widgets (React)](https://github.com/concurhaskell/concur-react-examples/blob/master/src/PipeWidgets.hs) - [Demo](https://concurhaskell.github.io/concur-react-examples/pipes.jsexe/index.html) - Your first 8 Concur Pipe programs! Inspired from the mighty Fudgets' - http://www.altocumulus.org/Fudgets/Intro/
