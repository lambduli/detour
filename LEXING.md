# Lexical Analysis


How do I parse the specific syntax of the Fitch-style notation?


```
| p1 : _A
| p2 : _B
|--------------
|
| x : | p3 : _C
|     |------------
|     |
|     |
|     |
|
|
```

So how do I correctly process this so that it looks something like this:

```
BEGIN_LAYOUT
p1 : _A
p2 : _B
--------------

x : BEGIN_LAYOUT p3 : _C
    ------------
    
    
    END_LAYOUT

END_LAYOUT
```

The rule for the layout is quite simple.
When I read `|` I look at the current layout-start.

If the current layout is smaller than the position of `|`,
this symbol is the start of the new layout.
```
|-----------
|
| |
```

If the current layout is equal to the position of `|`,
then this symbol is just a part of the current sub-proof, we ignore it.
```
|-----------
|
|
```

If the current layout is larger than the position of the `|`,
then there are multiple possibilities.
```
|------------
|
| |--------
| |
|
```
It is possible that this `|` will be followed by another one that will
be equal to the current layout.
It is also possible that it will be followed by one more—in that case that's a new layout-begin.
It is also possible that it will not be followed by another `|` at this line,
this would mean that we are ending one or more layouts.

```
|------------
|
| |--------
| |
| | |-------
| | |
|
```

It would also make sense to check that each non-beginning `|` is at the same
position as on the line above.
However, how would we make sure that we don't skip positions?
I could read those pipes with a function. It would get called when we see the first pipe at the beginning of the line. It would then read the input until it would read all the consecutive pipes. I would have to implement some sort of a `peek` or `unread'char` function, but that would be easy.


However, I must not rely on newlines as the pipe can even after some characters `x : |`.



So here's what I have to do when I see a pipe:

I check the current position and compare it with the current layout.
If the current position is larger than the current layout—I push a new layout.

If the current position is equal to the current layout—I don't do anything.

If the current position is smaller than the current layout—I set a start code stating that I am behind the layout. Inside this start code, I can read the pipe and nothing.
If I read a pipe, I run the same function.
If I can't read a pipe, I must read nothing so I unset the behind-start code and continue parsing. This makes it possible to read an identifier and the `:` and start a new layout or to read anything else.


This way I don't check everything. I don't check misaligned lines, I don't check skipped lines.