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

    public MyClass(): void => {
        printf("self::x = %d, self::y = %d\n", self::x, self::y);
    }
}

let main(): int => {
    let instance => @new MyClass(69, 420);
    instance::method();
    return 0;
}
```
