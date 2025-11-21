# Unilang Compiler

## ⚠️ This compiler is a work in progress.

## Quickstart
### building
```sh
cargo install --git https://github.com/Paul-Passeron/unilang
```
### usage
```sh
unilang main.ul -o main
```

## What is Unilang ?

Unilang is a statically typed, templated and procedural programming language supporting some object oriented constructs.

Unilang is meant to easily interop with C and leverage the power of its ecosystem.

## Example

### Hello World

```unilang
@include std::io

let main(): int => {
    printf("Hello, World !\n");
    return 0;
}
```

```sh
./main
# > Hello, World !
```

### Classes
```unilang
@include std::io

class MyClass => {
    private x: int;
    private y: int;

    public MyClass(x: int, y: int) => {
        self::x => x;
        self::y => y;
    }

    public method(): void => {
        printf("self::x = %d, self::y = %d\n", self::x, self::y);
    }
}

let main(): int => {
    let instance => @new MyClass(69, 420);
    instance::method();
    return 0;
}
```

### Impls
```unilang
@include std::io

class <T> A => {
    public x: T;
    public A(x: T) => {
        self::x => x;
    }
}

class B => {
    public padding: int;
    public B() => {
        self::padding => 0;
    }
}

impl A<int> => {
    public from_int(y: int): int => {
        return self::x + y;
    }
}

impl A<B> => {
    public from_B(y: int): int => {
        return y * y;
    }
}

let main(): int => {
    let ai => @as A<int> 45;
    let ab => @as A<B> (@as B ());
    let i => ai::from_int(24);
    let j => ab::from_B(24);

    printf("i = %d\n", i);
    printf("j = %d\n", j);

    return 0;
}
```
