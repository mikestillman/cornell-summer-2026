-*
One way to compute the lenght of a module is to compute the composition series
for the module. If we have a presentation for the module then we 
can construct a starting chain for the module using the generators

More specifically, if M is a finitely generated R-module with generators
$x_1, \cdots, x_n$ then we have a chain
M = <x_0, \cdots, x_n> \supset <x_0, \cdots, x_{n-1}> \supset ... \supset <x_0>
\supset 0
This may not be a composition series, but we can inspect the partial quotients 
and if they are not simple we should be able to find something to lift?
*- 

-*
Here is an example, let $R = k[x]$ and $M = R/(x^n)$ for some $n$.
This module has a composition series
\[
0 \subset (x^{n-1})/(x^n) \subset (x^{n-2})/(x^n) \subset \cdots \subset
R/(x^n). 
\]
and so has length $n$.

However, consider the generating set of $M$ as an $R$-module. Every element in
$M$ is of the form $a_0 + a_1 x + \cdots + a_{n-1}x^{n-1}$. Over $R$ a
generating set is simply $1 \in M$. 

This finitely generated module is described by the short exact sequence
0 \to R^1 \to{x^n} R^1 \to{1} R/(x^n) \to 0
*- 

-- Here is some experimentation with some examples
kk = ZZ/32003;
R = kk[x];
I = ideal x^5
M = R^1/I
res M -- Quesiton: is there a difference between `res M` and `freeResolution M`?

restart;
kk = ZZ/32003;
R = kk[x,y];
I = ideal(x^2,y^2);
M = R^1/I
res M
 
restart;
kk = ZZ/32003;
R = kk[x,y,z];
I = ideal(x,y,z);
M = R^1/I;
res M

restart;
kk = ZZ/32003;
R = kk[x,y];
I = (ideal(x,y))^2;
M = R^1/I;
res M
-- Perhaps let's write up this example?