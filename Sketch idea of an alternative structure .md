Sketch idea of an alternative structure of floats.

The primary idea is to merge the concepts of `FloatFormat` and the type implementing the data-structure of floats.  
The main benefit is that this avoids duplicating much functionality and possibly(?) allows lifting proofs to be simpler. There's also the fact that it is more general.

```lean
inductive Fp (F : FloatDesc) where
| NaN : Fp F
| Infinity : Fp F
| Finite : FiniteFp -- has a FloatDesc field
```
For example.  
However, `FloatDesc` would not be the fundamental data-type, but rather simply a common one. It would have the usual stuff that `FloatFormat` has currently.  

We would have a typeclass of `FloatLike` (can't name it `Float` because that's already taken).  
It would have the basic operations that floats support.
```lean
class FloatLike where
  prec : Nat
  emax : Int
  -- ...
```

`Fp`, for example, would simply dispatch to its `FloatDesc` field for much of that functionality.

We would then have functions on `FloatLike` that hopefully manage to avoid much of the individual behavior of the underlying type.  
There are several questions that arise, though.

1. What would the design for the functions look like?

Some of the rounding and other functions make sense when considering the FloatLike as a number, do we implement it in terms of `toRat`? Or what? Converting into the format seems kinda hard.  

2. What other typeclasses would we need?

We could have, for example, the `StandardFloatLike` which has that `emin = 1 - emax` and the like.  
Then there's whether there are multiple `NaN` values.

3. How do we handle conversion?

We could have specific functions, an `Fp.toFloatBits` for example.  
An alternative method would be to have a way to automatically route it, so that if there's many types it can move between them without too much hassle. I don't think this is easy though, and it'd probably be kindof arcane due to being a list of types implementing `FloatLike` with some conversion functions between them and finding the right path on the graph.

4. What about functions to get the fields of floating point values?

Since we can't match on it, this makes `.exponent` and `.significand` a bit awkward for NaN/Infinite values.  
But we already have this problem with `FloatBits`, so this isn't new.  
It would be best to just have them return a garbage value in that case, with an `exponent?` that returns `none` for non-finite values.  

My main class of uncertainty is how much this will actually improve implementing complex functions like `add`.  
`FloatBits` may very well have a quite natural implementation (since floats are meant to be represented in that format), but I'm not sure about the others.  
Then again, moving to `FloatBits` isn't that much work, the only real problem is proving various properties. So a general approach can work, with `FloatLike` having functions like `FloatLike.exponent` and the like, though I expect it to tend up with garbage like "FloatBits.exponent + bias + garbage = (FloatBits.biasedExponent - bias) + bias + garbage"—essentially redoing work. But it would be worse to reimplement all the functions on each type.

So I'm leaning towards a yes.  

5. Should we have `FloatLike` hold a function to get the `FloatDesc`? Or should it be an essemblage of functions on `FloatLike` for those properties?

I think the latter is more natural for typeclasses, being extendable by further typeclasses in a way that `FloatDesc` isn't really made for? (but could be done)


Observation:
This would make it easier to just have a type: `type BF16 = Fp (FloatDesc.BF16)` rather than a weird instance of the `FloatFormat` typeclass.