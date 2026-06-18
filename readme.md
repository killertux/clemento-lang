# ClementoLang

ClementoLang is my hobby programming language. It is a concatenative language inspired by Forth, Porth and Kitten. It has static typing and it is designed to be functional.

## It is prod ready?

**NOOOOO!!!!** . I am doing this for fun and learning purposes. Do not use it in production. The syntax is still in flux and the implementation is not optimized for performance.

## Roadmap

- [x] Static typing
- [x] ADT (Algebraic data type)
- [X] Compile
- [X] Lists
- [X] Quotation (Functions as first class)
- [ ] Dependency management
- [X] String as lists
- [ ] Permissions system or use monads
- [ ] Create a proper documentation
- [ ] Better tooling
- [ ] Self-host

## A little bit about the language

### Basic types

First and foremost, ClementoLang is statically typed. For know, we have the following basic types:

* U8
* U16
* U32
* U64
* U128
* I8
* I16
* I32
* I64
* I128
* F64
* Boolean
* String

Integer number by default are I64 and float number are F64. But you can be explicit about the type by using the following syntax:

```ClementoLang
42i32
98u8
-10i16
3.14f64
```

### Functions

Functions are typed by how they affect the stack. So for example + can be defined as follows:

```ClementoLang
def + (I64 I64 -> I64)
```

It takes two integers and returns an integer. We also have generics, they are defined as lowercase letters.
We also have function overloading. So if you define the same function multiple times, the compiler will choose the one that matches the types of the arguments on the stack going through the order of definition.

Functions can be defined using one of the following:

- `def <symbol> <body>`
- `defp <symbol> <body>`
- `defx <symbol>`

`def` defines a function that can be called from anywhere.
`defp` defines a private function that can only be called from within the module.
`defx` defines a external function that can be called from anywhere. External functions are either built-in or linked.

ClemetoLang has type inference. But it is not perfect yet. Especially when working with generics.

### Block

Block are used to group statements together. They are defined using the following syntax:

```ClementoLang
{
    <expression>
    <expression>
    ...
}
```

Block also create a new scope. Inside a block you can create new definitions (functions) that will be visible only within the block.

### Functions as values (quotations)

Writing a function's name invokes it. To push a function onto the stack *as a value* instead, prefix it with a backslash:

* `\name` (or `\mod::name`) pushes a reference to a named definition — or to a builtin such as `\+`, `\swap`, `\dup`.
* `\{ ... }` pushes an anonymous **quotation** (an inline function). Its type is inferred from its body (against an empty stack, so under-flowed operands become its inputs: `\{ 1i64 + }` has type `(I64 -> I64)`).

A function value has a function type, e.g. `(I64 -> I64)`. Run the value on top of the stack with the `apply` word — it pops the function and applies it to the values beneath it:

```ClementoLang
3i64 \{ 1i64 + } apply   // -> 4i64   (inline quotation)
5i64 \double apply       // -> 10i64  (named reference)
```

Function values can be passed to and stored by other definitions, enabling higher-order functions. A function type is written like any stack effect and can nest:

```ClementoLang
// take a value and a function, and apply the function twice
def twice (I64 (I64 -> I64) -> I64) {
    dup rot swap apply swap apply
}

5i64 \double twice       // -> 20i64
```

Quotations capture nothing — they operate purely on the stack — so they are plain function pointers with no allocation.

Function values can be **polymorphic**. A reference like `\dup` (type `(a -> a a)`) or a quotation like `\{ dup }` is left generic; its concrete type is discovered from the `apply` sites that consume it, and one monomorphic implementation is emitted per concrete type. Generic higher-order definitions work the same way — each instantiation is its own specialization:

```ClementoLang
def with (a (a -> a) -> a) { apply }

7i64 \double with   // -> 14i64   (instantiated at I64)
'a'  \bang   with   // -> '!'     (instantiated at Char)
```

A function value whose concrete type can't be inferred from its uses must be applied (or annotated) so it can be resolved. See `examples/first-class-functions.clem` and `examples/first-class-functions-poly.clem` for full walk-throughs.

Generic definitions can also **construct** generic values, so a real generic `map` over a list works — applying a function value to every element and rebuilding the list, monomorphized per element type:

```ClementoLang
def map (list::List<a> (a -> a) -> list::List<a>) {
    swap
    match {
        [] -> { drop list::Empty }
        [head ... tail] -> { dup tail swap map  swap head swap apply  list::List }
    }
}

[1i64 2i64 3i64] \double map   // List<I64>
"abc" \bang map                // List<Char> ("abc" -> "!!!")
```

See `examples/generic-constructors.clem`.

### Importing

Importing is done using the `import` keyword. For example:

```ClementoLang
import std::math
import std::*
```
