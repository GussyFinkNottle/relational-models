# relational-models
Models of dependent type-theory using binary relations for types, and diagonal elements for terms.

In 2013 Per Martin-Lof gave some Ernest Nagel Lectures in Philosophy & Science  at CMU. 
https://www.cmu.edu/dietrich/philosophy/events/nagel-lectures/past-lectures.html
These were videos of these lectures.

The the topic of the lectures was a general construction that equips
each type-forming operator in type-theory "tt" with a counter-part, that deals
with relations between pairs of such objects.  The counter-part is a proper
extension "tt++" of tt. 

I recently viwed the recordings, and decided to investigate this construction for
a few type-forming operators, using Agda.  I have treated a simple universe, bool, nat, 
disjoint union, sigma, pi, w-types , Petersonn-Synex trees, and the
identity type in both the "least reflexive" form, and the Paulin-Mohring form.
(Thanks to Fredrik.Nordvall-Forsberg for help with these.)
I think the agda files might interest someone.

The most natural, if banal thing to do would be us the construction to
define an extensional identity type for each type. 
For base types, it is clear what to do, though not
easy to show the relations are transitive. 

Another natural, if unpleasing thing to do would be to investigate
iterating this construction, which would involve "nesting", rather
as with identity types Id (Id (Id A a b) c d) e f. 

I think it is probably impossible that any form of uniform transport 
(as with the identity type) holds even for numerical and boolean equality, 
without presupposing "0, 1 and 2", meaning 
an empty universe 0, (giving ex-falso in various forms)
an singleton universe 1 (containing a single code for the empty set), and 
a boolean universe 2 with just codes for both 0 and 1. (As with von Neumann's 2.)



