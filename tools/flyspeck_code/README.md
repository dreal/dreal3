Generate SMT2 formulae from Flyspeck
====================================

Required Packages
-----------------

 1. Check-out Flyspeck

    ```
    svn checkout http://flyspeck.googlecode.com/svn/trunk/ flyspeck
    ```

 2. Check out HOL Light

    ```
    svn checkout http://hol-light.googlecode.com/svn/trunk/ hol-light
    ```


Instructions
------------

 1. Modify ``load.hl`` such that ``<FLYSPECK_DIR>`` points to your flyspeck directory.
   Modify ``load.hl`` such that ``<HOLLIGHT_DIR>`` points to your hollight directory.
   ``load.hl`` and ``parse.hl`` should copied to ``<FLYSPECK_DIR>/text_formalization``

 2. Navigate to ``<HOLLIGHT_DIR>``

    ```
    $ cd <HOLLIGHT_DIR>
    ```

 3. Load ocaml

    ```
    ocaml
    ```

 4. Load hol

    ```
    #use "hol.ml";;
    ```

 5. Navigate ``text_fromalization`` directory from inside HOL.

    ```
    #cd <FLYSPECK_DIR>/text_formalization
    ```

 6. Load ``load.hl`` which loads flyspeck and its dependencies.

    ```
    #use "load.hl";;
    ```

 7. Load ``parse_ineq.hl``

    ```
    #use "parse_ineq.hl";;
    ```

Notes: ``parse_ineq.hl`` generates the ``.range``, ``.formula``, and ``.dr`` files to ``/tmp`` directory. Output directory can be changed by modifying ``parse_ineq.hl`` code. Hol-light should be compiled from source code.


Usage
-----

```
#use "hol.ml";;
#cd "<FLYSPECK/text_formalization";;
#use "load_nonlinear.hl";; (<- original: parse_ineq.hl)
#use "parse_ineq2.hl";;
```

Authors
-------
 * 2012/08/10: Michael Wang <mswang12@gmail.com>
 * 2013/05/02: Soonho Kong <soonhok@cs.cmu.edu>
