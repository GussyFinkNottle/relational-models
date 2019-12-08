# relational-models
Models of dependent type-theory using binary relations for types, and diagonal elements for terms.

In 2013 Per Martin-Lof gave some a Ernest Nagel Lecture in Philosophy & Science  at CMU. 
<https://www.cmu.edu/dietrich/philosophy/events/nagel-lectures/past-lectures.html>
These were videos of these lectures.

The the topic of the lectures was a general construction that equips
each type-forming operator in type-theory "tt" with a counterpart, that deals
with relations between pairs of such objects.  The counterpart is
defined in a proper extension "tt++" of tt. 

Having looked at the recordings, I decided to investigate this construction for
a few type-forming operators, using Agda.  I've done bool, nat, 
disjoint union, sigma, pi, w-types , Petersonn-Synex trees, a simple
universe,  and the identity type in both the "least reflexive" form,
and the Paulin-Mohring form.

I think the agda files might interest someone.

(Thanks to Fredrik.Nordvall-Forsberg for help with the identity
types.)

The most natural, if banal thing to do would be us the construction to
define an extensional identity type for each type. 
For base types, it is clear what to do, though not
easy to show the relations are transitive. 

Another natural, if unattractively strenuous thing to do would be to
think about iterating this construction.
This would involve "nesting", rather
as with identity types Id (Id (Id A a b) c d) e f. 

It is difficult to see how any form of uniform/polymorphic "transport"
(as with the identity type) holds even for numerical and boolean equality, 
without presupposing some of "0, 1 and 2", meaning 

* an empty universe 0, (giving ex-falso in various forms)
* a singleton universe 1 (containing a single code for 0), and 
* a boolean universe 2 with just codes for both 0 and 1. (Like von Neumann 2.)

There is such a suggestion in <https://projecteuclid.org/euclid.jsl/1183742723> .



