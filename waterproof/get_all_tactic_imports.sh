#!/bin/bash
# Used generate the lines for AllTactics.v

find tactics | sed s:/:.:g | grep -e ".*.v$" |sed s:.v:.:g | sed "s:^:Require Export Waterproof.:g"
