#!/bin/bash
# Remove files produced by compilation,
# but no source code files.

find . | egrep "\.vos|\.vok|\.vo|\.glob|\.aux" | xargs rm -v

