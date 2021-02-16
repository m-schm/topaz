# Topaz

Topaz is a dependently typed language in a very early stage of development that
primarily compiles to JavaScript, but may acquire WASM/etc backends in the
future.

## Summary jargon list

It has / is planned to have:

- dependent types
- universe polymorphism
- row polymorphism
- call-by-value semantics by default, but can be overridden
- easy JS FFI à la PureScript
- irrelevant argument erasure
- type-case (requires the above)
- linear/affine types (tentative)

## Motivation / Inspiration

This is a bit of a missing point in the design space - PureScript doesn't offer
the full power of dependent types, while Agda isn't primarily meant for web
development and is incredibly intimidating to newcomers. Inspired by ReasonML
(now ReScript) and Elm, Topaz is aiming to be a more approachable to leverage
the flexibility and correctness provided by dependent types.

Some syntax has been taken from [Olle Fredriksson's
Sixten](https://github.com/ollef/sixten), particularly the usage of
TypeApplications-style `@` for implicit arguments and `type` for (G)ADT
declarations.

## "Dependent types"?

In a dependently typed language, types are themselves a special kind of value,
of type `Type`. While mind-bending at first, it allows type signatures to be
extremely specific, meaning you get more guarantees about what your code can and
can't do.

```
;; This is a comment

;; `Vec n a` represents lists that are `n` long, that contain `a`s
;; A Vec is either:
type Vec (n: Nat) (a: Type) =
  ;; empty, with length 0
  Nil: {a} -> Vec 0 a
  ;; 1 item longer than a Vec of length n
  `::`: {n a} -> a -> Vec n a -> Vec (n+1) a

;; Enforce that the two lists are the same length
let zip {n a b} (left: Vec n a) (right: Vec n b): Vec n (a, b) =
  match left, right in
    ;; Either both lists are empty...
    Nil,     Nil     => Nil
    ;; or they both contain at least one item.
    x :: xs, y :: ys => (x, y) :: zip xs ys
    ;; No other cases are needed, because the lists are the same length!
```

In fact, what other languages call "generics" are entirely absent in Topaz!
Instead, it's accomplished through passing the type in as an argument:

```
let doNothing (a: Type) (x: a): a = x

doNothing Int 3 ;; => 3
```

Writing out the type like this every time is tedious, though, so instead an
"implicit argument" is used:

```
let doNothing {a: Type} (x: a): a = x
;;            ^       ^ note the curly brackets!
doNothing 3 ;; => 3
```

These are filled in by the compiler during typechecking, and will throw an error
if there's any ambiguity. You can fill them in yourself using `@`:

```
doNothing @String "hello"
doNothing @(Array Int) [2, 3, 4]
```

