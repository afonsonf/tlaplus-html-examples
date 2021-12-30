--------------------- CONFIG MissionariesAndCannibals_Anim ---------------------
CONSTANTS
c1 = c1 c2 = c2 c3 = c3
m1 = m1 m2 = m2 m3 = m3
Cannibals    = {c1,c2,c3}
Missionaries = {m1,m2,m3}

INIT Init
NEXT Next
INVARIANT Inv

ALIAS Alias
VIEW View
================================================================================

--------------------- MODULE MissionariesAndCannibals_Anim ---------------------

EXTENDS TLC, IOUtils, Sequences

\* Variables and Constants from Spec
CONSTANTS Missionaries, Cannibals
VARIABLES bank_of_boat, who_is_on_bank, who_moved

\* Set a view because who_moved is an extra variable for the visualization
View == <<bank_of_boat, who_is_on_bank>>

Model == INSTANCE MissionariesAndCannibals
Template == INSTANCE MissionariesAndCannibals_Template

Init == Model!Init
Next == Model!Next

Inv == Model!Inv

templateVars == [
    bank_of_boat   |-> bank_of_boat,
    who_is_on_bank |-> who_is_on_bank,
    who_moved      |-> who_moved
]

filename == "html-example/inv/" \o ToString(TLCGet("level")) \o ".html"
Alias ==[filename |-> filename,
         print    |-> Serialize(Template!Template(templateVars),filename,
                        [format      |-> "TXT",
                         charset     |-> "UTF-8",
                         openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>])]

================================================================================
