------------------- CONFIG MissionariesAndCannibals_Template -------------------

================================================================================

------------------- MODULE MissionariesAndCannibals_Template -------------------

EXTENDS TLC, IOUtils, Sequences, Integers, HTML

LEVEL == TLCGet("level")
MAXLEVEL == TLCGet("diameter")

\***** Scripts

NavigationScriptListener(prev, next) ==
    HTMLJSKeyListener(<<
        HTMLJSNavigationKey("ARROWLEFT", prev \o ".html"),
        HTMLJSNavigationKey("ARROWRIGHT", next \o ".html")
    >>)

NavigationScript ==
    HTMLScript(<<
        LET prev_page_number == IF LEVEL = 1 THEN 1 ELSE LEVEL-1
            next_page_number == IF LEVEL = MAXLEVEL THEN MAXLEVEL ELSE LEVEL+1
        IN NavigationScriptListener(
            ToString(prev_page_number), ToString(next_page_number))
    >>)

\***** Template Main

HTMLTemplate == Deserialize("template/MissionariesAndCannibals_Template.html",
                    [format |-> "TXT", charset |-> "UTF-8"]).stdout

PeopleOnIsland(vars, side) ==
    IF side = vars.bank_of_boat
    THEN ToString(vars.who_is_on_bank[side] \ vars.who_moved) \o ", Boat: " \o ToString(vars.who_moved)
    ELSE ToString(vars.who_is_on_bank[side])

ClassOfBoat(vars, side) ==
    IF side = vars.bank_of_boat
    THEN ""
    ELSE "visibility: hidden;"

Template(vars) == StringFill(HTMLTemplate, <<
    <<"%depth%", ToString(LEVEL)>>,
    <<"%islandW%", PeopleOnIsland(vars, "W") >>,
    <<"%islandE%", PeopleOnIsland(vars, "E") >>,
    <<"%hiddenBoatW%", ClassOfBoat(vars, "W") >>,
    <<"%hiddenBoatE%", ClassOfBoat(vars, "E") >>,
    <<"%navigationScript%", NavigationScript >>
>>)

\***** Test Template

testVars == [
    bank_of_boat |-> "E",
    who_is_on_bank |-> [E |-> {"c1", "m1", "m2", "m3"}, W |-> {"c2", "c3"}],
    who_moved |-> {"c1","m2"}
]

ASSUME PrintT(Serialize(Template(testVars), "html-example/test/test.html",
           [format      |-> "TXT",
            charset     |-> "UTF-8",
            openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>]))
================================================================================
