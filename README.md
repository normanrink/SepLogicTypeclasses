
## Coq typeclasses for specification of object-oriented code with templates/generics.

Modern object-oriented programming languages like C++, Java and Rust support generic programming.
In C++ this is facilitated by _templates_.
For example, a generic list `List<T>` can be implemented
where the template parameter `T` can later be instantiated with any type.
When the sizes of objects can change dynamically, as is the case e.g. for lists,
these objects are typically allocated on the heap.
This naturally leads to the question of how separation logic can be used to reason about templated/generic object-oriented code.

This project develops a simple example of how Coq typeclasses can be used to reason about templated objects with separation logic.
The idea is that a typeclass specifies restrictions on the template parameter `T` used in a templated definition.
Specifically, we define a typeclass `MyObject` that essentially requires that a type name `T` has
a method `new` for allocation/construction and 
a method `del` for deallocation/destruction.
We then specify and implement methods `newList` and `delList` for constructing and destructing lists.
The specifications suffice to show that `List<T>` satisfies our typeclass `MyObject` provided `T` satisfies this typeclass.


### Acknowledgement

The definition of Hoare triples used in this project is loosely based on the presentation in
[Formal Reasoning About Programs](http://adam.chlipala.net/frap/) by Adam Chlipala.
