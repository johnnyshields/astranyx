//! Content and surface flags for collision filtering.
//!
//! These flags determine what gets hit during traces and what properties
//! surfaces have for gameplay purposes.

use serde::{Deserialize, Serialize};

/// Content flags describe what type of volume something is.
///
/// Used to filter collision traces - you can ignore certain content types
/// when tracing (e.g., ignore triggers when doing physics, ignore corpses
/// when shooting).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct ContentFlags(pub u32);

impl ContentFlags {
    /// Empty space - nothing here.
    pub const EMPTY: Self = Self(0);

    /// Solid world geometry - walls, floors, etc.
    pub const SOLID: Self = Self(1 << 0);

    /// Water volume - affects movement speed and allows swimming.
    pub const WATER: Self = Self(1 << 1);

    /// Lava volume - deals damage on contact.
    pub const LAVA: Self = Self(1 << 2);

    /// Slime volume - deals damage and slows movement.
    pub const SLIME: Self = Self(1 << 3);

    /// Player clip - blocks players but not projectiles.
    pub const PLAYER_CLIP: Self = Self(1 << 4);

    /// Monster clip - blocks NPCs but not players.
    pub const MONSTER_CLIP: Self = Self(1 << 5);

    /// Projectile clip - blocks projectiles but not players.
    pub const PROJECTILE_CLIP: Self = Self(1 << 6);

    /// Trigger volume - activates events when entered.
    pub const TRIGGER: Self = Self(1 << 7);

    /// Teleporter - instantly moves player to destination.
    pub const TELEPORTER: Self = Self(1 << 8);

    /// Jump pad - applies upward velocity.
    pub const JUMP_PAD: Self = Self(1 << 9);

    /// Player body - collision with player entities.
    pub const PLAYER_BODY: Self = Self(1 << 10);

    /// Corpse - dead entity, usually passable.
    pub const CORPSE: Self = Self(1 << 11);

    /// Detail brush - doesn't affect BSP splitting (rendering only).
    pub const DETAIL: Self = Self(1 << 12);

    /// Standard mask for player movement traces.
    pub const MASK_PLAYER_SOLID: Self = Self(
        Self::SOLID.0 | Self::PLAYER_CLIP.0 | Self::PLAYER_BODY.0,
    );

    /// Standard mask for projectile traces.
    pub const MASK_PROJECTILE: Self = Self(
        Self::SOLID.0 | Self::PROJECTILE_CLIP.0 | Self::PLAYER_BODY.0,
    );

    /// Standard mask for NPC movement.
    pub const MASK_NPC_SOLID: Self = Self(
        Self::SOLID.0 | Self::MONSTER_CLIP.0 | Self::PLAYER_BODY.0,
    );

    /// Check if these flags contain a specific flag.
    #[inline]
    pub fn contains(self, other: Self) -> bool {
        (self.0 & other.0) == other.0
    }

    /// Check if any of the given flags are set.
    #[inline]
    pub fn intersects(self, other: Self) -> bool {
        (self.0 & other.0) != 0
    }

    /// Combine two flag sets.
    #[inline]
    pub fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    /// Remove flags from this set.
    #[inline]
    pub fn difference(self, other: Self) -> Self {
        Self(self.0 & !other.0)
    }
}

impl std::ops::BitOr for ContentFlags {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        Self(self.0 | rhs.0)
    }
}

impl std::ops::BitAnd for ContentFlags {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self {
        Self(self.0 & rhs.0)
    }
}

/// Surface flags describe properties of a surface.
///
/// These affect gameplay interactions like footstep sounds, bullet impacts,
/// and movement behavior.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct SurfaceFlags(pub u32);

impl SurfaceFlags {
    /// No special properties.
    pub const NONE: Self = Self(0);

    /// No damage from falling on this surface.
    pub const NO_DAMAGE: Self = Self(1 << 0);

    /// Slippery surface - reduced friction.
    pub const SLICK: Self = Self(1 << 1);

    /// Sky surface - projectiles disappear, no collision response.
    pub const SKY: Self = Self(1 << 2);

    /// Ladder surface - allows climbing.
    pub const LADDER: Self = Self(1 << 3);

    /// No footstep sounds on this surface.
    pub const NO_STEPS: Self = Self(1 << 4);

    /// No bullet impact effects.
    pub const NO_IMPACT: Self = Self(1 << 5);

    /// No bullet marks/decals.
    pub const NO_MARKS: Self = Self(1 << 6);

    /// Flesh surface - blood effects, meat sounds.
    pub const FLESH: Self = Self(1 << 7);

    /// Metal surface - metallic impact sounds.
    pub const METAL: Self = Self(1 << 8);

    /// Wood surface - wooden impact sounds.
    pub const WOOD: Self = Self(1 << 9);

    /// Glass surface - can shatter.
    pub const GLASS: Self = Self(1 << 10);

    /// Gravel/dirt surface - dusty footsteps.
    pub const GRAVEL: Self = Self(1 << 11);

    /// Snow surface - crunchy footsteps.
    pub const SNOW: Self = Self(1 << 12);

    /// Check if these flags contain a specific flag.
    #[inline]
    pub fn contains(self, other: Self) -> bool {
        (self.0 & other.0) == other.0
    }
}

impl std::ops::BitOr for SurfaceFlags {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        Self(self.0 | rhs.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_content_flags_operations() {
        let solid = ContentFlags::SOLID;
        let water = ContentFlags::WATER;
        let combined = solid | water;

        assert!(combined.contains(solid));
        assert!(combined.contains(water));
        assert!(!combined.contains(ContentFlags::LAVA));
        assert!(combined.intersects(solid));
    }

    #[test]
    fn test_player_mask() {
        let mask = ContentFlags::MASK_PLAYER_SOLID;
        assert!(mask.contains(ContentFlags::SOLID));
        assert!(mask.contains(ContentFlags::PLAYER_CLIP));
        assert!(!mask.contains(ContentFlags::WATER));
    }
}
