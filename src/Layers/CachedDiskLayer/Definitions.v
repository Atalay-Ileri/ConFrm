Require Import Framework.
Require Import DiskLayer CacheLayer.
Import ListNotations.

Set Implicit Arguments.

Module CachedDiskOperation := HorizontalComposition CacheHL.Lang DiskHL.Lang.
Module CachedDiskHL := HoareLogic CachedDiskOperation.
Export CachedDiskHL.