Here are a few potential research projects on top of Argosy. We're not actively working on these, but they would improve the framework and some of them could lead to something interesting in their own right.

# Improvements to the framework

## Crashes during initialization

Handle crashes during initialization.

This should be symmetric with recovery, albeit with much simpler code and invariants for actual applications. Some things I discovered from trying this out:

- Initialization cannot guarantee that if it fails nothing happened. The problematic case comes in transitivity: if the lower level succeeds but the higher level fails, there's no possibility of reverting initialization but the overall initialization needs to fail.
- The fact that initialization can fail makes using the relation algebra more complicated than recovery.

This doesn't seem particularly important to the verification story, but it would be metatheoretically appealing to treat initialization the same as recovery.

## Refine to efficient code

Refine the shallow embedding to deeply-embedded, efficient code in a systems language.

This is better than directly writing code in a low-level language since it can separate out the functional aspects from implementation decisions.

One complication: an implementation is code written against the interface of the lower level, which needs to compose with an implementation of the lower level. In Gallina the composition is handled by a simple recursive substitution; the deep embedding needs to support composition, and ideally without fully inlining (eg, instead _link_ the high-level code to the low-level code). In fact, we probably don't want to commit to a set of low-level primitives, so the deep embedding should support a flexible set of primitives analogous to the `Op` type constructor.

## Horizontal composition

This is a big one that would make the framework a lot more realistic, although we've avoided needing it.

# Improvements to verification infrastructure

This includes the current examples, using CHL, and new approaches to proving refinements.

## Improve the examples

- Provide an asynchronous disk model and reasoning principles for it. We should at least be able to replicate FSCQ's disk model; can we do better?
- Use separation logic within a layer. Can this make verification easier? Can we make the automation more robust?
- Add a new lab for POCS.

## Ghost state

Figure out what exactly the story with ghost state is.

What is the minimal infrastructure needed for ghost state within the CHL framework, and what can we build on top of it?

## Use relation algebra for CHL
Unify CHL and the relation library better.

Some Hoare rules should naturally follow from relation rules. The connection to the particular shape of spec expected by recovery refinement should be more clear; we currently don't have a bundle that proves recovery refinement using appropriate CHL specs.

## Use relations for layer semantics and abstraction relations

Use relations to specify layers in a way that supports better connections to refinement. In particular, can we develop a weakest precondition calculus and enough simplification rules to calculationally prove refinements, at least for our simple examples? How do we incorporate the abstraction relation? Can we get the entire refinement proof just out of idiosyncratic properties of the abstraction relation?

These are probably two separate ideas, and using relations just for the semantics would already be a big improvement. It lets us re-use infrastructure, leads to readable semantics, allows abstracting away common patterns within and across semantics, makes it easier to track that every case is handled, and could plausibly be debugged with an execution engine (that is, Ltac that computes some path the the semantics for some inputs).
