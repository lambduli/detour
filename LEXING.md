# Lexical Analysis

## The Current Syntax

So here's what I have to do when I see a pipe:

I check the current position and compare it with the current layout.
If the current position is larger than the current layout—I push a new layout.

If the current position is equal to the current layout—I don't do anything.

If the current position is smaller than the current layout—I set a start code stating that I am behind the layout. Inside this start code, I can read the pipe and nothing.
If I read a pipe, I run the same function.
If I can't read a pipe, I must read nothing so I unset the behind-start code and continue parsing. This makes it possible to read an identifier and the `:` and start a new layout or to read anything else.


This way I don't check everything. I don't check misaligned lines, I don't check skipped lines.


## Hypothetical More Readable Syntax

I am thinking about a different syntax.

```
theorem foo : A ==> B ==> C, K, P  ⊢  B ==> A ==> C
{ assume p : A ==> B ==> C
  assume _ : K
  assume _ : P

  0 : {
    assume p0 : B

    1 : { assume p1 : A

          b=>c : B ==> C  by rule ==>-elim on p, p1
          C  by rule ==>-elim on b=>c, p0
        }

    A ==> C  by rule ==>-intro on 1
  }

  B ==> A ==> C  by rule ==>-intro on 0
}
```

Compare to the current syntax.

```
theorem foo : A ==> B ==> C ⊢ B ==> A ==> C
| p : A ==> B ==> C
|----------------------------
|
| 0 : | p0 : B
|     |---------------------
|     |
|     | 1 : | p1 : A
|     |     |------------------
|     |     |
|     |     | b=>c : B ==> C  by rule ==>-elim on p, p1
|     |     |
|     |     | C  by rule ==>-elim on b=>c, p0
|     |
|     | A ==> C  by rule ==>-intro on 1
|
| B ==> A ==> C  by rule ==>-intro on 0
```