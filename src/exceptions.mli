type wexn = NonExistingDataset of string

val throw : ?info:Exninfo.info -> wexn -> 'a
