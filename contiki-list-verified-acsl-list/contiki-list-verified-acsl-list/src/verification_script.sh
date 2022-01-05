#! /bin/bash

# Copyright (c) 2018, Inria, CEA, Northern Arizona University.
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions
# are met:
# 1. Redistributions of source code must retain the above copyright
#    notice, this list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright
#    notice, this list of conditions and the following disclaimer in the
#    documentation and/or other materials provided with the distribution.
# 3. Neither the name of the Institute nor the names of its contributors
#    may be used to endorse or promote products derived from this software
#    without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE INSTITUTE AND CONTRIBUTORS ``AS IS'' AND
# ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED.  IN NO EVENT SHALL THE INSTITUTE OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
# OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
# HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
# LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
# OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
# SUCH DAMAGE.
#
# This file is part of the verification of the Contiki operating system.
#
# Authors: - Allan Blanchard <mail@allan-blanchard.fr>
#          - Nikolai Kosmatov <nikolai.kosmatov@cea.fr>
#          - Frédéric Loulergue <frederic.loulergue@nau.edu>

TIMEOUT=700
PROCESSES=2
MACHINE=$(hostname)
SCRIPT=all_lemmas_proofs.script

function kill_provers {
    for solver in why3server cvc4 alt-ergo ; do
	for pid in $(pgrep $solver) ; do
	    echo "Kill: " $pid ;
	    kill -9 $pid ;
	done ;
    done
}

PROVERS=alt-ergo,cvc4-15
FUNCTIONS=list_remove,list_add,list_init,list_head,list_tail,list_pop,list_length,list_item_next,list_push,list_chop,list_copy,list_insert,list_force_insert,list_split
ALL_FUNCTIONS=$(echo $FUNCTIONS | tr ',' '\n')
STRUCTURES=list,list_ptr,list_point

WITHOUT_LEMMAS=no
WITHOUT_FUNCTIONS=no
WITHOUT_VALID_TESTS=no
WITH_INVALID_TESTS=no

function print_help {
    echo "By default, this script, on each data structure \"list\" \"list_ptr\" \"list_point\""
    echo "    - runs the coq proofs of the lemmas"
    echo "    - runs the proofs of all functions in the module"
    echo "    - runs the proofs of the valid user code functions"
    echo "    - skips the proofs of the invalid user code functions (that takes a lot of time since it has to fail)"

    echo "OPTIONS:"
    echo "    -only-one-structure :"
    echo "        only run the specified verification on \"list\""
    echo "    -without-lemmas :"
    echo "        skips the proofs of the lemmas"
    echo "    -only-functions=[functions,comma_separated]"
    echo "        only execute the proof of the specified functions"
    echo "        deactivate all other proofs (lemmas and tests)"
    echo "        only prove for the \"list\" structure"
    echo "    -without-functions=[functions,comma_separated]"
    echo "        skips the (specified) functions"
    echo "        If no function is specified, skips all of them"
    echo "    -without-valid-tests"
    echo "        skips the valid user code functions"
    echo "    -with-invalid-tests"
    echo "        force the proofs of the invalid tests"
}

for opt in "$@" ; do
    list=$(echo "$opt" | cut -s -d\= -f2)
    opt=$(echo "$opt" | cut -d\= -f1)
    
    case $opt in
	-help)
	    print_help
	    exit
	    ;;
	-only-one-structure)
	    STRUCTURES=list
	    ;;
	-without-lemmas)
	    WITHOUT_LEMMAS=yes
	    ;;
	-without-functions)
	    if [ "$list" == "" ] ; then
		WITHOUT_FUNCTIONS=yes
	    else
		WITHOUT_FUNCTIONS=some
		REMOVE_FUNCTIONS=$list
	    fi
	    ;;
	-only-functions)
	    if [ "$list" == "" ] ; then
		echo "-only-functions cannot be used without arguments"
		exit
	    else
		ALL_FUNCTIONS=$list
		WITHOUT_LEMMAS=yes
		WITHOUT_VALID_TESTS=yes
		WITH_INVALID_TESTS=no
		STRUCTURES=list
		break
	    fi
	    ;;
	-without-valid-tests)
	    WITHOUT_VALID_TESTS=yes
	    ;;
	-with-invalid-tests)
	    WITH_INVALID_TESTS=yes
	    ;;
	*)
	    echo "Invalid argument: $opt"
	    exit
    esac
done

if [ $WITHOUT_FUNCTIONS == some ] ; then
    REMOVE_FUNCTIONS=$(echo $REMOVE_FUNCTIONS | tr ',' '\n')
    FUNCTIONS=$(printf "$ALL_FUNCTIONS\n$REMOVE_FUNCTIONS" | sort -d | uniq -u)
else
    FUNCTIONS=$ALL_FUNCTIONS
fi
FUNCTIONS=$(echo $FUNCTIONS | tr ' ' ',')
STRUCTURES=$(echo $STRUCTURES | tr ',' '\n')

function proofs_no_lemmas_for {
    (time\
	 frama-c $1.c\
	 -wp\
	 -wp-par=$PROCESSES\
	 -wp-prover=$PROVERS\
	 -wp-timeout=$TIMEOUT\
	 -wp-prop=-@lemma,-EASY_Left,-EASY_Right\
	 -wp-fct=$FUNCTIONS\
	 -then\
	 -wp-rte\
	 -wp\
	 -wp-prop=-@lemma,-EASY_Left,-EASY_Right\
	 -wp-fct=$FUNCTIONS\
	 -then\
	 -wp-timeout=20\
	 -wp-prover=coq\
	 -wp-script=$SCRIPT\
	 -wp-prop=EASY_Left,EASY_Right\
     	 -wp-fct=$FUNCTIONS
    ) | tee verification_$1_${MACHINE}.txt ;
    kill_provers
}

function proofs_only_lemmas_for {
    (time\
	 frama-c $1.c\
	 -wp\
	 -wp-par=$PROCESSES\
	 -wp-prover=alt-ergo,coq\
	 -wp-timeout=30\
	 -wp-prop=@lemma\
	 -wp-script=$SCRIPT
    ) | tee verification_$1_lemmas_${MACHINE}.txt
    kill_provers
}

function valid_tests_for {
    (time\
	 user_code_tests/script.sh "$1.c" user_code_tests/valid.c
    ) | tee verification_$1_success_tests_${MACHINE}.txt
    kill_provers
}

function invalid_tests_for {
    (time\
	 user_code_tests/script.sh "$1.c" user_code_tests/invalid.c
    ) | tee verification_$1_success_tests_${MACHINE}.txt
    kill_provers
}

for example in $STRUCTURES ; do
    if [ $WITHOUT_LEMMAS == no ] ; then
	proofs_only_lemmas_for $example
    fi
    if [ ! $WITHOUT_FUNCTIONS == yes ] ; then
	proofs_no_lemmas_for $example
    fi
    if [ $WITHOUT_VALID_TESTS == no ] ; then
	valid_tests_for $example
    fi
    if [ $WITH_INVALID_TESTS == yes ] ; then
	invalid_tests_for $example
    fi
done
