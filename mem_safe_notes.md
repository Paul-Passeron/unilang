# Notes on move semantics for **Unilang**

```unilang
let x: t => y;
```
if y is trivially copyable or implements some kind of NoMove interface then it is simply copied.
Otherwise, it is moved.


```NoMove``` is a marker interface that must be specified by the user, not the compiler (except for primitive types). It is then checked at compile time that the inner components of the type are all marked ```NoMove``` as well (Or else you could have a wrapper for a type that does not implement NoMove implementing it)

```unilang
interface NoMove T => {}
```

## Example:
```unilang
class ShouldMove => { public inner   : void *;     }
class Wrapper    => { public wrapped : ShouldMove; }
```
```unilang
impl NoMove for Wrapper => {} // This will not compile.
```

Maybe such a feature could be made available on the user-level too,
Something like
```unilang
interface NoMove T where $T impl NoMove => {}
```
Meaning that for T to implement NoMove, all its inner types must implement NoMove (marked by the $T).

This maybe is a stupid idea with no real use case but this could help implement NoDrop for types that do not implement Droppable like
```unilang
impl <T impl !Droppable> NoDrop for T where $T impl NoDrop => {}
```
Where ```T impl !Droppable``` means that T does not implement Droppable. There is no conflict with the ```Droppable``` auto implementation because it is checked after. This would work for non-marker interfaces (like with actual content) but I don't really see how you could leverage this except for added constraints (you cannot programmatically reason on a type's fields in the language's user-space)

Here is a simple idea for the Clone interface
```unilang
interface Clone T => {
    clone(): T;
}
```
---
## On move semantics
### Function arguments
Let's assume that for the moment, for a function `f` that takes arguments `a` and `b` of types `ta` and `tb` respectively.
Consider the following snippet:
```unilang
let f(a: ta, b: tb): void => {
    ...
}

let foo(): void => {
    let x: ta => ...;
    let y: tb => ...;
    f(x, y);
    ...
}
```

I think this should mean that x and y are "*whatever happens when they are assigned to something else*" (either moved or copied)

You could also have something like:

```unilang
let f(ref a: ta, b: tb): void => {
    ...
}

let foo(): void => {
    let x: ta => ...;
    let y: tb => ...;
    f(x, y);
    ...
}
```

Where a will be passed by reference (I think there is no way around adding them to the language, this also means distinguishing self arg types in methods (static vs moved vs ref))

What do we do differently than Rust then ? 

The borrow checker might be easier that I thought to implement (at least a dumbed down version):

```Rust
fn test() {
    // '1:
    {
        let y: &i32; 
        // Lifetime of y is '1 so it expects a lifetime '2
        // such that '2 lives at least as long as '1
        
        // '2 ('2 < '1):
        {
            // Lifetime of x is '2
            let x = 2;
            y = &x; // Here, the assignement needs '1 >= '2 but '2 < '1 so it fails
        }

        // use y
        let _ = y;
    }
}
```

- Each scope gets its lifetime. We keep track of order constraints on the life times.
- If a value is still borrowed when dropped and the owner(s) isn't / aren't all dropped too, we have an error because a ref is dropped while still in use
- If a value is already borrowed (as mut or not), it cannot be borrowed as mutable a second time
- Lifetimes parameters are needed for types that use references
- Is there a better notation that 'a, '1, 'context, ... ?
- Move semantics become easier. If a value is going out of scope and it hasn't been moved then we can safely drop it assuming no previous error (If it implements Droppable and do nothing otherwise).
- Create drop implementation for every type that needs it (type that needs to be dropped but the Droppable interface is not implemented in user-land)

