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
    
INVARIANT
    etudiants <: ETUDIANT
    & modules <: MODULE
    & groupes <: GROUPE
    & projets <: PROJET
    
    & inscritA : etudiants <-> modules
    & moduleDe : projets --> modules
    & groupesDe : etudiants <-> groupes
    & affecteA : projets <-> etudiants
    
    & !mm.( mm : MODULE => 
        ( !ee.( (ee : ETUDIANT) =>
                	( card( affecteA~[{ee}] /\ moduleDe~[{mm}] ) <= 1 ) )
         ))
     

INITIALISATION
    etudiants := {}
    || modules := {}
    || groupes := {}
    || projets := {}
    
    || inscritA := {}
    || moduleDe := {}
    || groupesDe := {}
    || affecteA := {}
    
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
        
        /* L'étudiant n'est pas déjà inscrit à mm */
        & ee |-> mm /: inscritA
        
        /* l'étudiant n'est pas affecté à un projet de mm */
        & mm |-> ee /: (moduleDe~ ; affecteA)
        
    THEN
        inscritA := inscritA \/ {ee |-> mm}
    END
    ;
    
    desinscrire_etudiant_module(ee, mm) =
    PRE
        ee : ETUDIANT
        & ee : etudiants
        & mm : MODULE
        & mm : modules
        
        /* L'étudiant est inscrit à mm */
        & ee |-> mm : inscritA
        
    THEN
        /* Desinscrire l'étudiant + le désafecter des projets */
        inscritA := inscritA - {ee |-> mm}
        || ANY projet WHERE projet : PROJET & projet = moduleDe~(mm) THEN
            affecteA := affecteA - { projet |-> ee }
        END
    END
    ;
    
    inscrire_etudiant_projet(ee, pp) =
    PRE
        ee : ETUDIANT
        & ee : etudiants
        & pp : PROJET
        & pp : projets
        
        /* l'étudiant ne travaille pas déjà sur un projet du même module que pp */
        & card( moduleDe~[{moduleDe(pp)}] /\ affecteA~[{ee}] ) = 0
        
        /* l'étudiant est inscrit au module */
        & ee : inscritA~[moduleDe[{pp}]]
    THEN
        affecteA := affecteA \/ {pp |-> ee}
    END
    ;
    
    desinscrire_etudiant_projet(ee, pp) =
    PRE
        ee : ETUDIANT
        & ee : etudiants
        & pp : PROJET
        & pp : projets
        
        /* l'étudiant travaille sur pp */
        & pp |-> ee : affecteA
    THEN
        affecteA := affecteA - {pp |-> ee}
    END
    ;
    
    /*affecter_groupe(gg, pp) =
    PRE
        gg : GROUPE
        & gg : groupes
        & pp : PROJET
        & pp : projets
        
        le projet n'est pas déjà affecté
        & affecteA[{pp}] :{}
        
        aucun étudiant du groupe n'est déjà affecté à un projet du même module
        & moduleDe[{pp}] /<: moduleDe[affecteA~[groupesDe[groupesDe~[{gg}]]]]
    THEN
        affecteA := affecteA \/ {pp |-> gg}
    END
    ;*/
    
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
    
    /* Pourquoi on peut pas prouver ??
    On vérifie que mm et pp ne sont dans aucune relation
    L'invariant devrait être vérifié....*/
    ajouter_projet(pp, mm) =
    PRE
        pp : PROJET
        & pp /: projets
        & mm : MODULE
        & mm : modules
        & mm /: ran(inscritA)
        & mm /: ran(moduleDe)
        & pp /: dom(affecteA)
        & pp /: dom(moduleDe)
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
     * return : Nombre de projets sur lequel travaille l'étudiant et ensemble de ces projets
     */
    nn,pp <-- liste_projets(ee) =
    PRE
        ee : ETUDIANT
        & ee : etudiants
    THEN
        pp := affecteA~[{ee}]
        || nn := card(affecteA~[{ee}])
    END
    ;
   
    
    /*
     * QUESTION 1.E
     */
    ee <-- participent_a_plus_de(nn) =
    PRE
        nn : NAT
    THEN
        ANY etudiant WHERE etudiant : ETUDIANT & etudiant : etudiants THEN
        	ee := ee \/ {etudiant}
        END

    END
    
END
