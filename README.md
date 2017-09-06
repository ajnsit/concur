# Concur

A brand new client side Web UI framework for Haskell that explores an entirely new paradigm. It does not follow FRP (think Reflex or Reactive Banana), or Elm architecture, but aims to combine the best parts of both.

It has two backends -

1. [React](https://github.com/facebook/react) based, called [concur-react](concur-react).
2. [Virtual-Dom](https://github.com/Matt-Esch/virtual-dom) based, called [concur-vdom](concur-vdom).

There are more backends in the works, including one for [React-Native](https://github.com/facebook/react-native), and for Native UI toolkits like [FLTK](https://github.com/deech/fltkhs).

The aim is to have a consistent API for all backends, so for example, a web app using react can simply be recompiled as a native GUI. Of course, any native react widgets used by the app would have to be ported to the native platform as well. 

## Why Concur

### The UI problem

There are lots of options for building web UIs. I have built large UIs with Plain Javascript, Angular, React, Elm, and Reflex, among others. However something seems to be missing from all of them.

1. JS based UI libs tend to be very unstructured and require a lot of effort from the programmer to keep things maintainable. React is the only exception I've seen, however it too comes with its own complications due to the fact that it is written in JS.
2. Elm has a lot of things going for it, but ultimately, "The Elm Architecture" feels very constrained. There are many well known abstractions for structuring code that we would like to use, but can't. For example, we can't use monads to build UIs incrementally. There are no monad transformers, so no using StateT to manage state. Even the composability of multiple widgets suffers because of how rigidly we must adhere to the elm architecture and must loop everything throgh a state modification and a render function. This codebase started out as an attempt to keep Elm's advantages, while opening up new avenues to structuring code.
3. Reflex/FRP has brilliant ideas at its core but ultimately suffers from annoying flaws due to its flexibility and complexity. FRP is NOT the easiest model to think and reason about. I've also found it difficult to refactor. For example, if you have to extract a bunch of events from deep within the DOM (though that may just be my bad coding practices). There are unsolved problems (such as handling global popups) that usually necessitate peppering random IO effects throughout the codebase, which can cause race conditions. In my opinion, Reflex is currently the best solution for UIs, in that it gives you the full power of Haskell, and is quite fun to use, but it can be improved upon.

### The solution
This library was originally conceived as a way to improve Elm by adding -

1. Easy widget composition. If you have a `counter` widget, then adding two of them in the same page should be something as simple as `counter <|> counter`
2. Remove the focus on State modification. Make rendering a `Monad` so that it's possible to use `StateT` transformer to get easy state modification back.
3. Use *inversion of control* to make everything seem synchronous and simplify code. Waiting for a click event should be as simple as `click >>= doSomething` with no callbacks in sight.
4. Using inversion of control made effects more expressive, while still not as unstructured as Reflex. An effect in Concur is simply `IO a`. If you want to display a widget every 10 seconds, it's as simple as `forever $ liftIO (threadDelay 10*1000000) >> doSomething`. If you want to do the same thing every 10 seconds *and* on every click, it's as simple as `forever $ (getClick <|> liftIO (threadDelay 10*1000000) >>= doSomething`.
5. Eliminating the difference between state modification and view rendering. So a new widget can be simply - `div (class_ "hello") [text "Here are some widgets", counter, someOtherWidget]`. This wires up both the view rendering and the action handling for all nested widgets, without having to manually manage each separately.

### Examples (These are currently only the vdom backend examples)

1. [Click Counting Example](https://github.com/ajnsit/concur/blob/master/concur-vdom/examples/ClickCounter.hs) - [Demo](https://ajnsit.github.io/concur/examples/clickCounter.jsexe/index.html) - Count total number of clicks on the page, with a button that increments the click count by 10, and also autoincrement clicks every second.
2. [TodoMVC Example](https://github.com/ajnsit/concur/blob/master/concur-vdom/examples/Todos.hs) - [Demo](https://ajnsit.github.io/concur/examples/todos.jsexe/index.html) - The canonical TodoMVC example, with views modeled after the one in Elm.
3. [Mario Example](https://github.com/ajnsit/concur/blob/master/concur-vdom/examples/Mario.hs) - [Demo](https://ajnsit.github.io/concur/examples/mario.jsexe/index.html) - Port of the Mario example from Elm.
4. [High/Low Game Example](https://github.com/ajnsit/concur/blob/master/concur-vdom/examples/HiLo.hs) - [Demo](https://ajnsit.github.io/concur/examples/hilo.jsexe/index.html) - An extremely simple number guessing game in 15 lines of code.
5. [Kirby Super Star Ultra Splits Timer GUI Challange](https://github.com/ajnsit/concur/blob/master/concur-vdom/examples/KirbySuperStarUltra.hs) - [Demo](https://ajnsit.github.io/concur/examples/kssu.jsexe/index.html) - Concur implementation of the [KSSU Splits Timer GUI Challenge](https://gist.github.com/lexi-lambda/701f1f1282401059f13a4220e8178ba4). Shows a moderately complex UI that's not a todolist!

