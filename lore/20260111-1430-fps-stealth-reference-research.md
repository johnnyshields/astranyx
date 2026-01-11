# FPS/Stealth Game Reference Research

## Context

Research into open source codebases for implementing an MGS-style (Metal Gear Solid) FPS mode in Astranyx. Goal is a stealth-action third-person/first-person hybrid rather than pure twitch shooter.

## Key Open Source References

### Stealth Mechanics

| Project | Language | Link | Value |
|---------|----------|------|-------|
| **mgs_reversing** | C | [GitHub](https://github.com/FoxdieTeam/mgs_reversing) | MGS PSX reimplementation - actual Kojima code reverse engineered |
| **The Dark Mod** | C++ | [GitHub](https://github.com/stgatilov/darkmod_src) | idTech4-based stealth engine with vision cones, sound propagation, light-based hiding |
| **MetalGear (MSX2)** | ASM | [GitHub](https://github.com/GuillianSeed/MetalGear) | Fully annotated disassembly of original 1987 Metal Gear |
| **Stealth-Game** | C# | [GitHub](https://github.com/RaceMahoney/Stealth-Game) | Unity MGS-style prototype, good for gameplay patterns |

### FPS Movement

| Project | Language | Link | Value |
|---------|----------|------|-------|
| **Quake GPL** | C | [GitHub](https://github.com/id-Software/Quake) | The foundational FPS movement code, Source engine derives from this |
| **bevy_fps_controller** | Rust | [GitHub](https://github.com/qhdwight/bevy_fps_controller) | Source engine-style movement for Bevy, supports Rapier/Avian |
| **RustCycles** | Rust | [GitHub](https://github.com/rustcycles/rustcycles) | Third-person arena shooter using Fyrox engine |

### Camera Systems

| Project | Language | Link | Value |
|---------|----------|------|-------|
| **bevy_third_person_camera** | Rust | [GitHub](https://github.com/The-DevBlog/bevy_third_person_camera) | Third-person with offset, collision avoidance |
| **smooth-bevy-cameras** | Rust | [GitHub](https://github.com/bonsairobo/smooth-bevy-cameras) | Exponentially-smoothed FPS/orbit cameras |

## Key Insights

### From Quake Source

- Player movement in `sv_user.c` (server-side) and prediction in QuakeWorld
- [Fabien Sanglard's Quake Source Review](https://fabiensanglard.net/quakeSource/) explains architecture
- Network layer outputs to frames, picked up by prediction layer for collision

### From The Dark Mod

- Full stealth AI with vision cones and peripheral vision
- Sound propagation through environment
- Light gem system (how visible you are based on lighting)
- Alert state machine (unaware -> suspicious -> searching -> combat)

### From MGS Reversing

- Active project decompiling MGS Integral PC
- Can build and run from source for testing
- Reveals actual implementation of radar, alert phases, guard AI

## MGS Core Mechanics to Implement

1. **Vision Cone System**
   - Forward cone of vision (narrow, far)
   - Peripheral vision (wide, short)
   - Blocked by walls/obstacles
   - Affected by lighting level

2. **Alert State Machine**
   ```
   UNAWARE -> CURIOUS -> ALERT -> EVASION -> COMBAT -> SEARCH -> UNAWARE
   ```

3. **Sound Propagation**
   - Footsteps (affected by surface, crouch/run)
   - Gunfire (loud, alerts wide area)
   - Environmental (doors, broken glass)

4. **Radar/Soliton System**
   - Enemy positions and facing
   - Jammed during alert phases

5. **Cover System**
   - Wall press
   - Corner peek
   - Prone/crouch stealth

## Current State

Existing `astranyx-rs/crates/core/src/simulation/fps.rs` has:
- Basic WASD + mouse look movement
- 3D position with 2D projection for collisions
- Simple enemy AI (move toward player, shoot)
- Turret/on-rails mode

## Next Steps

1. Study The Dark Mod's AI vision system (`game/ai/` directory)
2. Implement vision cone raycasting in `fps.rs`
3. Add alert state machine to `Enemy` struct
4. Sound propagation system (simpler than TDM's acoustic model)
5. Third-person camera option with smooth-bevy-cameras style

## Resources

- [Quake Source Code Review](https://fabiensanglard.net/quakeSource/) - Architecture deep dive
- [The Dark Mod Wiki](https://wiki.thedarkmod.com/) - Stealth mechanics documentation
- [MGSV Modding Wiki](https://mgsvmoddingwiki.github.io/) - Modern MGS engine insights
