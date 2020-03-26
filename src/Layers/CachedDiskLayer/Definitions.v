Require Import Framework.
Require Import DiskLayer CacheLayer.
Import ListNotations.

Set Implicit Arguments.

Module CachedDiskOperation := HorizontalComposition CacheHL.Lang DiskHL.Lang.
Module CachedDiskHL := HoareLogic CachedDiskOperation.
Export CachedDiskHL.
Definition cached_disk_lts := Build_LTS CachedDiskHL.Lang.oracle CachedDiskHL.Lang.state CachedDiskHL.Lang.prog CachedDiskHL.Lang.exec.
