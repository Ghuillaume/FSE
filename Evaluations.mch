/* Evaluations
 * Author: 
 * Creation date: mer. nov. 20 2013
 */
MACHINE
    Evaluations
SETS
    ETUDIANT
    ; MODULE
    ; GROUPE
    ; PROJET
   
VARIABLES
    /* Sets */
    etudiants
    , modules
    , groupes
    , projets
    
    /* Relations */
    , inscritA
    , moduleDe
    , groupesDe
    , affecteA
    , contrainte
    
INVARIANT
    etudiants <: ETUDIANT
    & modules <: MODULE
    & groupes <: GROUPE
    & projets <: PROJET
    
    & inscritA : etudiants <-> modules
    & moduleDe : projets --> modules
    & groupesDe : etudiants <-> groupes
    & affecteA : projets +-> groupes
    
    & contrainte : moduleDe~ +-> (groupesDe ; affecteA~)
    
INITIALISATION
    etudiants := ETUDIANT
    || modules := MODULE
    || groupes := GROUPE
    || projets := PROJET
    
    || inscritA := {}
    || moduleDe := {}
    || groupesDe := {}
    || affecteA := {}
    || contrainte := {}
    
    
OPERATIONS
    
    /*
     * QUESTION 1.A
     */
    
    inscrire_etudiant_module(ee, mm) =
    PRE
        ee : ETUDIANT
        & ee : etudiants
        & mm : MODULE
        & mm : modules
        & mm /: inscritA[{ee}]
    THEN
        inscritA := inscritA \/ {ee |-> mm}
    END
    ;
    
    inscrire_etudiant_groupe(ee, gg) =
    PRE
        ee : ETUDIANT
        & ee : etudiants
        & gg : GROUPE
        & gg : groupes
        
        // l'étudiant n'est pas déjà membre du groupe
        & gg /: groupesDe[{ee}]
        
        // l'étudiant ne travaille pas déjà sur le module concerné par le groupe
        & moduleDe[affecteA~[{gg}]] /<: moduleDe[affecteA~[groupesDe[{ee}]]]
    THEN
        groupesDe := groupesDe \/ {ee |-> gg}
    END
    ;
    
    affecter_groupe(gg, pp) =
    PRE
        gg : GROUPE
        & gg : groupes
        & pp : PROJET
        & pp : projets
        
        // le projet n'est pas déjà affecté
        & affecteA[{pp}] :{}
        
        // aucun étudiant du groupe n'est déjà affecté à un projet du même module
        & moduleDe[{pp}] /<: moduleDe[affecteA~[groupesDe[groupesDe~[{gg}]]]]
    THEN
        affecteA := affecteA \/ {pp |-> gg}
    END
    ;
    
    /*
     * QUESTION 1.B
     */
     
    ajouter_module(mm) =
    PRE
        mm : MODULE
        & mm /: modules
    THEN
        modules := modules \/ {mm}
    END
    ;
    
    ajouter_groupe(gg) =
    PRE
        gg : GROUPE
        & gg /: groupes
    THEN
        groupes := groupes \/ {gg}
    END
    ;
    
    ajouter_projet(pp, mm) =
    PRE
        pp : PROJET
        & pp /: projets
        & mm : MODULE
        & mm : modules
    THEN
        projets := projets \/ {pp}
        || moduleDe := moduleDe \/ {pp |-> mm}
    END
    ;
    
    ajouter_etudiant(ee) =
    PRE
        ee : ETUDIANT
        & ee /: etudiants
    THEN
        etudiants := etudiants \/ {ee}
    END
    ;
   
    
    /*
     * QUESTION 1.C
     */
    gg <-- liste_groupes(ee) =
    PRE
        ee : ETUDIANT
        & ee : etudiants
    THEN
        gg := groupesDe[{ee}]
    END
    ;
   
    
    /*
     * QUESTION 1.D
     */
    pp <-- liste_projets(ee) =
    PRE
        ee : ETUDIANT
        & ee : etudiants
    THEN
        pp := affecteA~[groupesDe[{ee}]]
    END
    ;
   
    
    /*
     * QUESTION 1.E
     */
    ee <-- participent_a_plus_de(nn) =
    PRE
        nn : NATURAL1
    THEN
         
    END
    
END
