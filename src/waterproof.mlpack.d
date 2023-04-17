src/waterproof_MLPACK_DEPENDENCIES:=src/g_waterproof src/automation
src/g_waterproof.cmx : FOR_PACK=-for-pack Waterproof
src/automation.cmx : FOR_PACK=-for-pack Waterproof
src/waterproof.cmo:$(addsuffix .cmo,$(src/waterproof_MLPACK_DEPENDENCIES))
src/waterproof.cmx:$(addsuffix .cmx,$(src/waterproof_MLPACK_DEPENDENCIES))
