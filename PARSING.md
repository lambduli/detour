# Parsing

I need to figure out how to collect all the free-vars in the current scope.

Since the parsing is done DFS-style, I don't have much options.

One option is using the tying-the-know trick with attributes.

The other option is to parametrize the AST with the representation of the LEVEL (possibly).
Then there would be a function that would get the AST parametrized with `()` and with all the information in the state, it would re-interpret all the variables and constants.

I am still not sure why was I of the opinion that even constants that are unrestricted need to be tracked (their level).



I am actually picking a completely different route.
Parsing won't deal with levels.
The proof-checking will deal with it instead.
As I proof-check, I keep track of the depth.
There's a function, that when given a list of derivations, collects all the variables and constants in them but only goes one layer deep.
All of those, that are not yet tracked, get assigned the current level.
Only then are all of those derivations checked.

The unification then must check the escape using a monadic function that obtains those levels from the context (probably state) and compares them.
In a case, where some constant or a variable is not tracked by the context, we raise an internal error.

This simplifies things quite a bit.

Later, when a renamer is implemented this approach will work great.

Until then, I need to make sure that I don't introduce two variables in the scopes of the same depth sharing the name. That would cause some issues. After a renamer does its job, those two would have two completely different names, so no issue.