# lambda (to be named)

A pure functional programming language that compiles to PHP7

This started as a toy implementation of the HM type theory, but has been turning
into a full functional compiler project.

Example program:

```
data List a = Nil | Cons a (List a)

filter : forall a. (a -> Bool) -> List a -> List a
filter = rec filterRec pred input = case input of {
    Nil -> Nil;
    Cons a rest -> case pred a of {
        true -> Cons a (filterRec pred rest);
        false -> filterRec pred rest;
    };
}

test = filter (\x. x) (Cons true (Cons false (Cons true Nil)))
```

### Usage

1. `stack install`
2. `lambdac <source file>`

### Features

- Decidable type inference
- ADTs
- let, rec, and case statements
- Type signatures
- Higher kinded polymorphism
- Typeclasses

### Coming Soon

- Records
- Significant whitespace
- Infix operators
- see [full gitlab backlog](https://gitlab.com/LightAndLight/hindley-milner/boards) for more