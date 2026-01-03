# ClementoLang

ClementoLang is my hobby programming language. It is a concatenative language inspired by Forth, Porth and Kitten. It has static typing and it is designed to be functional.

## It is prod ready?

**NOOOOO!!!!** . I am doing this for fun and learning purposes. Do not use it in production. The syntax is still in flux and the implementation is not optimized for performance.

## Roadmap

- [x] Static typing
- [ ] ADT (Algebraic data type)
- [ ] Type Classes
- [X] Compile
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

### If and Else.

We can have single ifs, for example:

```ClementoLang
true if { "Hello World!" println }
```

We can have if-else statements, for example:

```ClementoLang
true if { "Hello World!" println } else { "Goodbye World!" println }
```

One important thing to note are the stack types. When we have a single if expression, without an else, we cannot change the stack type. So we either do not touch the stack at all, or we push values onto it with the exact same types. When we have an if-else statement, we can change the stack type. But both branches must have the same stack type.

### Importing

Importing is done using the `import` keyword. For example:

```ClementoLang
import std::math
import std::*
```
