------------------------------ CONFIG EWD998_Anim ------------------------------
CONSTANT N = 9 MAXLEVEL = 33
CONSTRAINTS StateConstraint
SPECIFICATION Spec
INVARIANT Inv
VIEW View
ALIAS Alias
CHECK_DEADLOCK FALSE
================================================================================

------------------------------ MODULE EWD998_Anim ------------------------------

EXTENDS TLC, IOUtils, Sequences

\* Variables and Constants from Spec
CONSTANTS N, MAXLEVEL
VARIABLES messages, active, color, counter, pending, token

Model == INSTANCE EWD998
Template == INSTANCE EWD998_Template

\* Set a view because messages is an extra variable for the visualization
View == <<active, color, counter, pending, token>>

Spec == Model!Spec
StateConstraint == Model!StateConstraint

Inv == Model!terminationDetected => TLCGet("level") # MAXLEVEL

templateVars == [
    pending  |-> pending,
    counter  |-> counter,
    token    |-> token,
    active   |-> active,
    color    |-> color,
    messages |-> messages
]

filename == "html-example/inv/" \o ToString(TLCGet("level")) \o ".html"
Alias ==[filename |-> filename,
         print    |-> Serialize(Template!Template(templateVars),filename,
                        [format      |-> "TXT",
                         charset     |-> "UTF-8",
                         openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>])]
================================================================================
