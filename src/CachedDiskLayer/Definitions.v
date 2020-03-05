Require Import Primitives Simulation Layer DiskLayer CacheLayer.
Import ListNotations.

Set Implicit Arguments.

Module CachedDiskOperation := HorizontalComposition CacheOperation DiskOperation.
Module CachedDiskHL := HoareLogic CachedDiskOperation.
Export CachedDiskOperation.
Export CachedDiskHL.
Hint Constructors exec.