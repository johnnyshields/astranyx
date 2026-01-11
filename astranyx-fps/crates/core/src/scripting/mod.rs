//! Rhai scripting integration for game content.
//!
//! Scripts define enemy behaviors, wave spawning, weapons, and powerups.
//! The engine provides deterministic execution of scripts for lockstep sync.

use std::collections::HashMap;
use std::path::Path;

use rhai::{Engine, AST, Scope, Dynamic, Map, Array};

/// Enemy stats loaded from script.
#[derive(Debug, Clone)]
pub struct EnemyStats {
    pub health: i32,
    pub speed: f32,
    pub points: u32,
    pub hitbox_radius: f32,
    pub fire_rate: u32,
}

impl Default for EnemyStats {
    fn default() -> Self {
        Self {
            health: 20,
            speed: 80.0,
            points: 50,
            hitbox_radius: 16.0,
            fire_rate: 90,
        }
    }
}

/// Script-friendly enemy data for update calls.
#[derive(Debug, Clone)]
pub struct ScriptEnemy {
    pub id: u32,
    pub x: f32,
    pub y: f32,
    pub vx: f32,
    pub vy: f32,
    pub health: i32,
    pub frame: u32,
}

impl ScriptEnemy {
    /// Convert to rhai Map for script calls.
    fn to_map(&self) -> Map {
        let mut map = Map::new();
        map.insert("id".into(), Dynamic::from(self.id as i64));
        map.insert("x".into(), Dynamic::from(self.x as f64));
        map.insert("y".into(), Dynamic::from(self.y as f64));
        map.insert("vx".into(), Dynamic::from(self.vx as f64));
        map.insert("vy".into(), Dynamic::from(self.vy as f64));
        map.insert("health".into(), Dynamic::from(self.health as i64));
        map.insert("frame".into(), Dynamic::from(self.frame as i64));
        map
    }
}

/// A loaded script with cached AST.
struct LoadedScript {
    ast: AST,
    stats: Option<EnemyStats>,
}

/// A loaded world script.
struct LoadedWorld {
    #[allow(dead_code)]
    ast: AST,
    #[allow(dead_code)]
    id: String,
    start_segment: String,
}

/// A loaded segment script.
struct LoadedSegment {
    ast: AST,
    #[allow(dead_code)]
    id: String,
}

/// The main script engine wrapper.
pub struct ScriptEngine {
    engine: Engine,
    enemy_scripts: HashMap<String, LoadedScript>,
    wave_script: Option<AST>,
    weapons_script: Option<AST>,
    powerups_script: Option<AST>,
    /// World scripts indexed by world ID.
    world_scripts: HashMap<String, LoadedWorld>,
    /// Segment scripts indexed by segment ID.
    segment_scripts: HashMap<String, LoadedSegment>,
    /// Route definitions script.
    route_script: Option<AST>,
    /// Game config script.
    config_script: Option<AST>,
}

impl ScriptEngine {
    /// Create a new script engine.
    pub fn new() -> Self {
        let mut engine = Engine::new();

        // Register math functions
        engine.register_fn("sin", |x: f64| x.sin());
        engine.register_fn("cos", |x: f64| x.cos());
        engine.register_fn("abs", |x: f64| x.abs());
        engine.register_fn("abs", |x: i64| x.abs());
        engine.register_fn("min", |a: i64, b: i64| a.min(b));
        engine.register_fn("min", |a: f64, b: f64| a.min(b));
        engine.register_fn("max", |a: i64, b: i64| a.max(b));
        engine.register_fn("max", |a: f64, b: f64| a.max(b));
        engine.register_fn("floor", |x: f64| x.floor());
        engine.register_fn("ceil", |x: f64| x.ceil());
        engine.register_fn("sqrt", |x: f64| x.sqrt());

        // Register placeholder functions that scripts call
        // These would normally interact with game state
        engine.register_fn("get_world_bounds", || {
            let mut map = Map::new();
            map.insert("min_x".into(), Dynamic::from(0.0_f64));
            map.insert("min_y".into(), Dynamic::from(0.0_f64));
            map.insert("max_x".into(), Dynamic::from(1920.0_f64));
            map.insert("max_y".into(), Dynamic::from(1080.0_f64));
            map
        });

        engine.register_fn("get_nearest_player", |_x: f64, _y: f64| {
            // Return player position (placeholder)
            let mut map = Map::new();
            map.insert("x".into(), Dynamic::from(200.0_f64));
            map.insert("y".into(), Dynamic::from(540.0_f64));
            map
        });

        engine.register_fn("normalize", |x: f64, y: f64| {
            let len = (x * x + y * y).sqrt();
            let mut map = Map::new();
            if len > 0.0 {
                map.insert("x".into(), Dynamic::from(x / len));
                map.insert("y".into(), Dynamic::from(y / len));
            } else {
                map.insert("x".into(), Dynamic::from(0.0_f64));
                map.insert("y".into(), Dynamic::from(0.0_f64));
            }
            map
        });

        // Placeholder functions for spawning (would queue commands)
        engine.register_fn("spawn_bullet", |_owner: &str, _x: f64, _y: f64, _vx: f64, _vy: f64, _damage: i64| {
            // Placeholder - would queue spawn command
        });

        Self {
            engine,
            enemy_scripts: HashMap::new(),
            wave_script: None,
            weapons_script: None,
            powerups_script: None,
            world_scripts: HashMap::new(),
            segment_scripts: HashMap::new(),
            route_script: None,
            config_script: None,
        }
    }

    /// Clear all loaded scripts (for hot-reloading).
    pub fn clear(&mut self) {
        self.enemy_scripts.clear();
        self.wave_script = None;
        self.weapons_script = None;
        self.powerups_script = None;
        self.world_scripts.clear();
        self.segment_scripts.clear();
        self.route_script = None;
        self.config_script = None;
    }

    /// Load all scripts from a directory.
    pub fn load_scripts_from_dir(&mut self, scripts_path: &Path) -> Result<(), Box<dyn std::error::Error>> {
        // Load enemy scripts
        let enemies_path = scripts_path.join("enemies");
        if enemies_path.exists() {
            for entry in std::fs::read_dir(&enemies_path)? {
                let entry = entry?;
                let path = entry.path();
                if path.extension().map(|e| e == "rhai").unwrap_or(false) {
                    let name = path.file_stem()
                        .and_then(|s| s.to_str())
                        .unwrap_or("unknown")
                        .to_string();
                    let script = std::fs::read_to_string(&path)?;
                    self.load_enemy_script_from_str(&name, &script)?;
                }
            }
        }

        // Load wave script
        let wave_path = scripts_path.join("waves/wave_system.rhai");
        if wave_path.exists() {
            let script = std::fs::read_to_string(&wave_path)?;
            self.load_wave_script_from_str(&script)?;
        }

        // Load weapons script
        let weapons_path = scripts_path.join("weapons/weapons.rhai");
        if weapons_path.exists() {
            let script = std::fs::read_to_string(&weapons_path)?;
            self.load_weapons_script_from_str(&script)?;
        }

        // Load powerups script
        let powerups_path = scripts_path.join("powerups/powerups.rhai");
        if powerups_path.exists() {
            let script = std::fs::read_to_string(&powerups_path)?;
            self.load_powerups_script_from_str(&script)?;
        }

        Ok(())
    }

    /// Load an enemy script from a string.
    pub fn load_enemy_script_from_str(&mut self, name: &str, script: &str) -> Result<(), Box<dyn std::error::Error>> {
        let ast = self.engine.compile(script)?;

        // Try to get stats from the script
        let stats = self.extract_enemy_stats(&ast);

        self.enemy_scripts.insert(name.to_string(), LoadedScript { ast, stats });
        Ok(())
    }

    /// Load wave system script from a string.
    pub fn load_wave_script_from_str(&mut self, script: &str) -> Result<(), Box<dyn std::error::Error>> {
        let ast = self.engine.compile(script)?;
        self.wave_script = Some(ast);
        Ok(())
    }

    /// Load weapons script from a string.
    pub fn load_weapons_script_from_str(&mut self, script: &str) -> Result<(), Box<dyn std::error::Error>> {
        let ast = self.engine.compile(script)?;
        self.weapons_script = Some(ast);
        Ok(())
    }

    /// Load powerups script from a string.
    pub fn load_powerups_script_from_str(&mut self, script: &str) -> Result<(), Box<dyn std::error::Error>> {
        let ast = self.engine.compile(script)?;
        self.powerups_script = Some(ast);
        Ok(())
    }

    /// Load a world script from a string.
    pub fn load_world_script_from_str(&mut self, name: &str, script: &str) -> Result<(), Box<dyn std::error::Error>> {
        let ast = self.engine.compile(script)?;

        // Extract world info
        let mut scope = Scope::new();
        let _ = self.engine.run_ast_with_scope(&mut scope, &ast);

        let world_info: Result<Map, _> = self.engine.call_fn(&mut scope, &ast, "get_world", ());
        let (id, start_segment) = match world_info {
            Ok(map) => {
                let id = map.get("id")
                    .and_then(|v| v.clone().into_string().ok())
                    .unwrap_or_else(|| name.to_string());
                let start = map.get("start_segment")
                    .and_then(|v| v.clone().into_string().ok())
                    .unwrap_or_default();
                (id, start)
            }
            Err(_) => (name.to_string(), String::new()),
        };

        self.world_scripts.insert(id.clone(), LoadedWorld { ast, id, start_segment });
        Ok(())
    }

    /// Load a segment script from a string.
    pub fn load_segment_script_from_str(&mut self, name: &str, script: &str) -> Result<(), Box<dyn std::error::Error>> {
        let ast = self.engine.compile(script)?;

        // Extract segment ID
        let mut scope = Scope::new();
        let _ = self.engine.run_ast_with_scope(&mut scope, &ast);

        let segment_info: Result<Map, _> = self.engine.call_fn(&mut scope, &ast, "get_segment", ());
        let id = match segment_info {
            Ok(map) => {
                map.get("id")
                    .and_then(|v| v.clone().into_string().ok())
                    .unwrap_or_else(|| name.to_string())
            }
            Err(_) => name.to_string(),
        };

        self.segment_scripts.insert(id.clone(), LoadedSegment { ast, id });
        Ok(())
    }

    /// Load route definitions script from a string.
    pub fn load_route_script_from_str(&mut self, script: &str) -> Result<(), Box<dyn std::error::Error>> {
        let ast = self.engine.compile(script)?;
        self.route_script = Some(ast);
        Ok(())
    }

    /// Load game config script from a string.
    pub fn load_config_script_from_str(&mut self, script: &str) -> Result<(), Box<dyn std::error::Error>> {
        let ast = self.engine.compile(script)?;
        self.config_script = Some(ast);
        Ok(())
    }

    /// Get the starting segment for a world.
    pub fn get_world_start_segment(&self, world_id: &str) -> Option<&str> {
        self.world_scripts.get(world_id).map(|w| w.start_segment.as_str())
    }

    /// Get the starting world from config script.
    pub fn get_start_world(&self) -> Option<String> {
        let ast = self.config_script.as_ref()?;

        let mut scope = Scope::new();
        let _ = self.engine.run_ast_with_scope(&mut scope, ast);

        let result: Result<String, _> = self.engine.call_fn(&mut scope, ast, "get_start_world", ());
        result.ok()
    }

    /// Get the first loaded world ID (fallback if no config).
    pub fn get_default_world(&self) -> Option<&str> {
        self.world_scripts.keys().next().map(|s| s.as_str())
    }

    /// Get segment configuration from script.
    pub fn get_segment_config(&self, segment_id: &str) -> Option<crate::level::SegmentConfig> {
        let segment = self.segment_scripts.get(segment_id)?;

        let mut scope = Scope::new();
        let _ = self.engine.run_ast_with_scope(&mut scope, &segment.ast);

        let map: Map = self.engine.call_fn(&mut scope, &segment.ast, "get_segment", ()).ok()?;

        Some(crate::level::SegmentConfig {
            id: map.get("id")
                .and_then(|v| v.clone().into_string().ok())
                .unwrap_or_else(|| segment_id.to_string()),
            name: map.get("name")
                .and_then(|v| v.clone().into_string().ok())
                .unwrap_or_default(),
            mode: self.extract_game_mode(&map),
            bounds: self.extract_bounds_3d(&map).unwrap_or_default(),
            camera: self.extract_camera_config(&map).unwrap_or_default(),
            backgrounds: self.extract_backgrounds(&map),
            duration: map.get("duration")
                .and_then(|v| v.as_int().ok())
                .map(|d| d as u32),
            scroll: self.extract_scroll_config(&map),
            wave_pool: map.get("wave_pool")
                .and_then(|v| v.clone().into_typed_array::<String>().ok())
                .unwrap_or_else(|| vec!["grunt".to_string()]),
            spawn_rate: map.get("spawn_rate")
                .and_then(|v| v.as_float().ok())
                .unwrap_or(1.0) as f32,
            difficulty_curve: map.get("difficulty_curve")
                .and_then(|v| v.clone().into_string().ok())
                .map(|s| crate::level::segment::DifficityCurve::from_string(&s))
                .unwrap_or(crate::level::segment::DifficityCurve::Linear),
            geometry: self.extract_geometry(&map),
            lights: self.extract_lights(&map),
            player_start: self.extract_player_start(&map),
        })
    }

    /// Extract geometry definitions from a script map.
    fn extract_geometry(&self, map: &Map) -> Vec<crate::level::GeometryDef> {
        let Some(geo_array) = map.get("geometry") else {
            return Vec::new();
        };

        let Ok(arr) = geo_array.clone().into_typed_array::<Map>() else {
            return Vec::new();
        };

        arr.iter().filter_map(|geo| {
            let geo_type = geo.get("type")?.clone().into_string().ok()?;

            let pos = geo.get("pos")?.clone().cast::<Map>();
            let position = glam::Vec3::new(
                pos.get("x").and_then(|v| v.as_float().ok()).unwrap_or(0.0) as f32,
                pos.get("y").and_then(|v| v.as_float().ok()).unwrap_or(0.0) as f32,
                pos.get("z").and_then(|v| v.as_float().ok()).unwrap_or(0.0) as f32,
            );

            let size_map = geo.get("size")?.clone().cast::<Map>();
            let size = glam::Vec3::new(
                size_map.get("x").and_then(|v| v.as_float().ok()).unwrap_or(1.0) as f32,
                size_map.get("y").and_then(|v| v.as_float().ok()).unwrap_or(1.0) as f32,
                size_map.get("z").and_then(|v| v.as_float().ok()).unwrap_or(1.0) as f32,
            );

            let color_map = geo.get("color")?.clone().cast::<Map>();
            let color = [
                color_map.get("r").and_then(|v| v.as_int().ok()).unwrap_or(128) as u8,
                color_map.get("g").and_then(|v| v.as_int().ok()).unwrap_or(128) as u8,
                color_map.get("b").and_then(|v| v.as_int().ok()).unwrap_or(128) as u8,
            ];

            // Parse solid flag (default: false)
            let solid = geo.get("solid")
                .and_then(|v| v.as_bool().ok())
                .unwrap_or(false);

            // Parse optional tag
            let tag = geo.get("tag")
                .and_then(|v| v.clone().into_string().ok());

            Some(crate::level::GeometryDef {
                geo_type,
                position,
                size,
                color,
                solid,
                tag,
            })
        }).collect()
    }

    /// Extract light definitions from a script map.
    fn extract_lights(&self, map: &Map) -> Vec<crate::level::LightDef> {
        let Some(lights_array) = map.get("lights") else {
            return Vec::new();
        };

        let Ok(arr) = lights_array.clone().into_typed_array::<Map>() else {
            return Vec::new();
        };

        arr.iter().filter_map(|light| {
            let light_type = light.get("type")
                .and_then(|v| v.clone().into_string().ok())
                .map(|s| crate::level::segment::LightType::from_string(&s))
                .unwrap_or(crate::level::segment::LightType::Point);

            let pos = light.get("pos")?.clone().cast::<Map>();
            let position = glam::Vec3::new(
                pos.get("x").and_then(|v| v.as_float().ok()).unwrap_or(0.0) as f32,
                pos.get("y").and_then(|v| v.as_float().ok()).unwrap_or(0.0) as f32,
                pos.get("z").and_then(|v| v.as_float().ok()).unwrap_or(0.0) as f32,
            );

            let color_map = light.get("color")?.clone().cast::<Map>();
            let color = [
                color_map.get("r").and_then(|v| v.as_int().ok()).unwrap_or(255) as u8,
                color_map.get("g").and_then(|v| v.as_int().ok()).unwrap_or(255) as u8,
                color_map.get("b").and_then(|v| v.as_int().ok()).unwrap_or(255) as u8,
            ];

            let intensity = light.get("intensity")
                .and_then(|v| v.as_float().ok())
                .unwrap_or(1.0) as f32;

            let range = light.get("range")
                .and_then(|v| v.as_float().ok())
                .unwrap_or(100.0) as f32;

            let spot_angle = light.get("spot_angle")
                .and_then(|v| v.as_float().ok())
                .map(|v| v as f32);

            let direction = light.get("direction")
                .map(|v| v.clone().cast::<Map>())
                .map(|d| glam::Vec3::new(
                    d.get("x").and_then(|v| v.as_float().ok()).unwrap_or(0.0) as f32,
                    d.get("y").and_then(|v| v.as_float().ok()).unwrap_or(-1.0) as f32,
                    d.get("z").and_then(|v| v.as_float().ok()).unwrap_or(0.0) as f32,
                ));

            Some(crate::level::LightDef {
                light_type,
                position,
                color,
                intensity,
                range,
                spot_angle,
                direction,
            })
        }).collect()
    }

    /// Extract player start position from a script map.
    fn extract_player_start(&self, map: &Map) -> Option<glam::Vec3> {
        let start = map.get("player_start")?.clone().cast::<Map>();
        Some(glam::Vec3::new(
            start.get("x").and_then(|v| v.as_float().ok()).unwrap_or(0.0) as f32,
            start.get("y").and_then(|v| v.as_float().ok()).unwrap_or(0.0) as f32,
            start.get("z").and_then(|v| v.as_float().ok()).unwrap_or(0.0) as f32,
        ))
    }

    /// Extract 3D bounds from a script map.
    fn extract_bounds_3d(&self, map: &Map) -> Option<crate::physics::WorldBounds3D> {
        let bounds = map.get("bounds")?.clone().cast::<Map>();
        Some(crate::physics::WorldBounds3D::new(
            bounds.get("min_x").and_then(|v| v.as_float().ok()).unwrap_or(0.0) as f32,
            bounds.get("min_y").and_then(|v| v.as_float().ok()).unwrap_or(0.0) as f32,
            bounds.get("min_z").and_then(|v| v.as_float().ok()).unwrap_or(-100.0) as f32,
            bounds.get("max_x").and_then(|v| v.as_float().ok()).unwrap_or(1920.0) as f32,
            bounds.get("max_y").and_then(|v| v.as_float().ok()).unwrap_or(1080.0) as f32,
            bounds.get("max_z").and_then(|v| v.as_float().ok()).unwrap_or(100.0) as f32,
        ))
    }

    /// Extract camera config from a script map.
    fn extract_camera_config(&self, map: &Map) -> Option<crate::level::CameraConfig> {
        let cam = map.get("camera")?.clone().cast::<Map>();

        let pos = cam.get("position")
            .map(|v| v.clone().cast::<Map>())
            .map(|p| glam::Vec3::new(
                p.get("x").and_then(|v| v.as_float().ok()).unwrap_or(960.0) as f32,
                p.get("y").and_then(|v| v.as_float().ok()).unwrap_or(540.0) as f32,
                p.get("z").and_then(|v| v.as_float().ok()).unwrap_or(1000.0) as f32,
            ))
            .unwrap_or(glam::Vec3::new(960.0, 540.0, 1000.0));

        let target = cam.get("target")
            .map(|v| v.clone().cast::<Map>())
            .map(|t| glam::Vec3::new(
                t.get("x").and_then(|v| v.as_float().ok()).unwrap_or(960.0) as f32,
                t.get("y").and_then(|v| v.as_float().ok()).unwrap_or(540.0) as f32,
                t.get("z").and_then(|v| v.as_float().ok()).unwrap_or(0.0) as f32,
            ))
            .unwrap_or(glam::Vec3::new(960.0, 540.0, 0.0));

        let follow_offset = cam.get("follow_offset")
            .map(|v| v.clone().cast::<Map>())
            .map(|o| glam::Vec3::new(
                o.get("x").and_then(|v| v.as_float().ok()).unwrap_or(0.0) as f32,
                o.get("y").and_then(|v| v.as_float().ok()).unwrap_or(0.0) as f32,
                o.get("z").and_then(|v| v.as_float().ok()).unwrap_or(500.0) as f32,
            ))
            .unwrap_or(glam::Vec3::new(0.0, 0.0, 500.0));

        Some(crate::level::CameraConfig {
            projection: cam.get("type")
                .and_then(|v| v.clone().into_string().ok())
                .map(|s| crate::level::CameraProjection::from_string(&s))
                .unwrap_or_default(),
            position: pos,
            target,
            fov: cam.get("fov").and_then(|v| v.as_float().ok()).unwrap_or(60.0) as f32,
            follow_player: cam.get("follow_player").and_then(|v| v.as_bool().ok()).unwrap_or(false),
            follow_offset,
            ..Default::default()
        })
    }

    /// Extract background layers from a script map.
    fn extract_backgrounds(&self, map: &Map) -> Vec<crate::level::BackgroundLayer> {
        let Some(bgs) = map.get("backgrounds") else {
            return Vec::new();
        };

        let Ok(arr) = bgs.clone().into_typed_array::<Map>() else {
            return Vec::new();
        };

        arr.iter().filter_map(|bg| {
            Some(crate::level::BackgroundLayer {
                layer: bg.get("layer")?.clone().into_string().ok()?,
                scroll_speed: bg.get("scroll_speed").and_then(|v| v.as_float().ok()).unwrap_or(1.0) as f32,
                z: bg.get("z").and_then(|v| v.as_float().ok()).unwrap_or(-100.0) as f32,
            })
        }).collect()
    }

    /// Extract game mode from a script map.
    fn extract_game_mode(&self, map: &Map) -> crate::level::GameMode {
        let mode_str = map.get("mode")
            .and_then(|v| v.clone().into_string().ok())
            .unwrap_or_default();

        // Extract path_id if present
        let path_id = map.get("path_id")
            .and_then(|v| v.clone().into_string().ok())
            .unwrap_or_default();

        match mode_str.as_str() {
            "side-scroll" | "sidescroll" => {
                let angle = map.get("angle")
                    .and_then(|v| v.as_float().ok())
                    .unwrap_or(0.0) as f32;
                crate::level::GameMode::SideScroll { angle }
            }
            "on-rails" | "onrails" | "rails" => {
                crate::level::GameMode::OnRails { path_id }
            }
            "free-flight" | "freeflight" => crate::level::GameMode::FreeFlight,
            "turret" => {
                crate::level::GameMode::Turret { path_id }
            }
            "first-person" | "firstperson" | "fps" => crate::level::GameMode::FirstPerson,
            _ => crate::level::GameMode::default(),
        }
    }

    /// Extract scroll config from a script map.
    fn extract_scroll_config(&self, map: &Map) -> Option<crate::level::ScrollConfig> {
        let scroll = map.get("scroll")?.clone().cast::<Map>();

        let enabled = scroll.get("enabled").and_then(|v| v.as_bool().ok()).unwrap_or(true);
        if !enabled {
            return None;
        }

        let dir = scroll.get("direction")
            .map(|v| v.clone().cast::<Map>())
            .map(|d| glam::Vec3::new(
                d.get("x").and_then(|v| v.as_float().ok()).unwrap_or(1.0) as f32,
                d.get("y").and_then(|v| v.as_float().ok()).unwrap_or(0.0) as f32,
                d.get("z").and_then(|v| v.as_float().ok()).unwrap_or(0.0) as f32,
            ))
            .unwrap_or(glam::Vec3::new(1.0, 0.0, 0.0));

        Some(crate::level::ScrollConfig {
            enabled: true,
            direction: dir,
            speed: scroll.get("speed").and_then(|v| v.as_float().ok()).unwrap_or(60.0) as f32,
        })
    }

    /// Call segment's on_enter callback.
    pub fn call_segment_on_enter(&self, segment_id: &str, level_state: &crate::level::LevelState) {
        let Some(segment) = self.segment_scripts.get(segment_id) else { return };

        let mut scope = Scope::new();
        let _ = self.engine.run_ast_with_scope(&mut scope, &segment.ast);

        let state_map = self.level_state_to_map(level_state);
        let _: Result<(), _> = self.engine.call_fn(&mut scope, &segment.ast, "on_enter", (state_map,));
    }

    /// Call segment's on_tick callback.
    pub fn call_segment_on_tick(&self, segment_id: &str, level_state: &crate::level::LevelState, frame: u32) {
        let Some(segment) = self.segment_scripts.get(segment_id) else { return };

        let mut scope = Scope::new();
        let _ = self.engine.run_ast_with_scope(&mut scope, &segment.ast);

        let state_map = self.level_state_to_map(level_state);
        let _: Result<(), _> = self.engine.call_fn(&mut scope, &segment.ast, "on_tick", (state_map, frame as i64));
    }

    /// Call segment's on_exit callback.
    pub fn call_segment_on_exit(&self, segment_id: &str, level_state: &crate::level::LevelState) {
        let Some(segment) = self.segment_scripts.get(segment_id) else { return };

        let mut scope = Scope::new();
        let _ = self.engine.run_ast_with_scope(&mut scope, &segment.ast);

        let state_map = self.level_state_to_map(level_state);
        let _: Result<(), _> = self.engine.call_fn(&mut scope, &segment.ast, "on_exit", (state_map,));
    }

    /// Convert LevelState to a rhai Map for script callbacks.
    fn level_state_to_map(&self, state: &crate::level::LevelState) -> Map {
        let mut map = Map::new();
        map.insert("world_id".into(), Dynamic::from(state.world_id.clone()));
        map.insert("segment_id".into(), Dynamic::from(state.segment_id.clone()));
        map.insert("segment_frame".into(), Dynamic::from(state.segment_frame as i64));
        map.insert("scroll_offset".into(), Dynamic::from(state.scroll_offset.x as f64));
        map.insert("enemies_killed".into(), Dynamic::from(state.enemies_killed as i64));
        map.insert("enemies_spawned".into(), Dynamic::from(state.enemies_spawned as i64));
        map.insert("boss_defeated".into(), Dynamic::from(state.boss_defeated));
        map.insert("secrets_found".into(), Dynamic::from(state.secrets_found as i64));
        map.insert("damage_taken".into(), Dynamic::from(state.damage_taken as i64));
        map
    }

    /// Get list of loaded world IDs.
    pub fn loaded_world_ids(&self) -> Vec<&str> {
        self.world_scripts.keys().map(|s| s.as_str()).collect()
    }

    /// Get list of loaded segment IDs.
    pub fn loaded_segment_ids(&self) -> Vec<&str> {
        self.segment_scripts.keys().map(|s| s.as_str()).collect()
    }

    /// Get routes from a specific segment.
    pub fn get_routes_from(&self, segment_id: &str) -> Vec<crate::level::Route> {
        let Some(ast) = &self.route_script else {
            return Vec::new();
        };

        let mut scope = Scope::new();
        let _ = self.engine.run_ast_with_scope(&mut scope, ast);

        let routes_result: Result<Array, _> = self.engine.call_fn(&mut scope, ast, "get_routes", ());

        let Ok(routes_array) = routes_result else {
            return Vec::new();
        };

        let mut routes: Vec<crate::level::Route> = routes_array
            .iter()
            .filter_map(|r| {
                let map = r.clone().cast::<Map>();
                let from = map.get("from")?.clone().into_string().ok()?;

                // Only include routes from the specified segment
                if from != segment_id {
                    return None;
                }

                let to = map.get("to")?.clone().into_string().ok()?;
                let trigger_map = map.get("trigger")?.clone().cast::<Map>();
                let trigger = crate::level::RouteTrigger::from_map(&trigger_map)?;

                let transition = map.get("transition")
                    .map(|t| {
                        let tmap = t.clone().cast::<Map>();
                        crate::level::Transition {
                            transition_type: tmap.get("type")
                                .and_then(|v| v.clone().into_string().ok())
                                .map(|s| crate::level::TransitionType::from_string(&s))
                                .unwrap_or_default(),
                            duration: tmap.get("duration")
                                .and_then(|v| v.as_int().ok())
                                .unwrap_or(30) as u32,
                            cutscene: tmap.get("cutscene")
                                .and_then(|v| v.clone().into_string().ok()),
                        }
                    })
                    .unwrap_or_default();

                let priority = map.get("priority")
                    .and_then(|v| v.as_int().ok())
                    .unwrap_or(0) as i32;

                Some(crate::level::Route {
                    from,
                    to,
                    trigger,
                    transition,
                    priority,
                })
            })
            .collect();

        // Sort by priority (higher first)
        routes.sort_by(|a, b| b.priority.cmp(&a.priority));

        routes
    }

    /// Extract enemy stats by calling get_stats() function.
    fn extract_enemy_stats(&self, ast: &AST) -> Option<EnemyStats> {
        // Run the script once to initialize constants, then call get_stats
        let mut scope = Scope::new();

        // First evaluate the script to define constants
        let _ = self.engine.run_ast_with_scope(&mut scope, ast);

        // Now call get_stats with the populated scope
        let result: Result<Map, _> = self.engine.call_fn(&mut scope, ast, "get_stats", ());

        result.ok().map(|map| {
            EnemyStats {
                health: map.get("health")
                    .and_then(|v| v.as_int().ok())
                    .unwrap_or(20) as i32,
                speed: map.get("speed")
                    .and_then(|v| v.as_float().ok())
                    .unwrap_or(80.0) as f32,
                points: map.get("points")
                    .and_then(|v| v.as_int().ok())
                    .unwrap_or(50) as u32,
                hitbox_radius: map.get("hitbox_radius")
                    .and_then(|v| v.as_float().ok())
                    .unwrap_or(16.0) as f32,
                fire_rate: map.get("fire_rate")
                    .and_then(|v| v.as_int().ok())
                    .unwrap_or(90) as u32,
            }
        })
    }

    /// Get stats for an enemy type.
    pub fn get_enemy_stats(&self, enemy_type: &str) -> Option<EnemyStats> {
        self.enemy_scripts.get(enemy_type)
            .and_then(|s| s.stats.clone())
    }

    /// Update an enemy using its script.
    /// Returns (vx, vy) velocity.
    pub fn update_enemy(&self, enemy_type: &str, enemy: &ScriptEnemy, dt: f32) -> Option<(f32, f32)> {
        let script = self.enemy_scripts.get(enemy_type)?;

        let enemy_map = enemy.to_map();
        let scope = Scope::new();

        let result: Result<Map, _> = self.engine.call_fn(
            &mut scope.clone(),
            &script.ast,
            "update",
            (enemy_map, dt as f64),
        );

        result.ok().map(|map| {
            let vx = map.get("vx")
                .and_then(|v| v.as_float().ok())
                .unwrap_or(-80.0) as f32;
            let vy = map.get("vy")
                .and_then(|v| v.as_float().ok())
                .unwrap_or(0.0) as f32;
            (vx, vy)
        })
    }

    /// Get available enemies for a wave number.
    pub fn get_available_enemies(&self, wave: u32) -> Vec<String> {
        let Some(ast) = &self.wave_script else {
            return vec!["grunt".to_string()];
        };

        let scope = Scope::new();
        let result: Result<Array, _> = self.engine.call_fn(
            &mut scope.clone(),
            ast,
            "get_available_enemies",
            (wave as i64,),
        );

        result.ok()
            .map(|arr| {
                arr.iter()
                    .filter_map(|v| v.clone().into_string().ok())
                    .collect()
            })
            .unwrap_or_else(|| vec!["grunt".to_string()])
    }

    /// Get list of loaded enemy type names.
    pub fn loaded_enemy_types(&self) -> Vec<&str> {
        self.enemy_scripts.keys().map(|s| s.as_str()).collect()
    }
}

impl Default for ScriptEngine {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_script_engine_creation() {
        let engine = ScriptEngine::new();
        assert!(engine.enemy_scripts.is_empty());
    }

    #[test]
    fn test_load_grunt_script() {
        let mut engine = ScriptEngine::new();
        let script = r#"
            const STATS = #{
                health: 20,
                speed: 80.0,
                points: 50,
                hitbox_radius: 16.0,
                fire_rate: 90,
            };

            fn get_stats() { STATS }

            fn update(enemy, dt) {
                let wave = sin(enemy.frame * 0.1) * 30.0;
                #{
                    vx: -STATS.speed,
                    vy: wave
                }
            }
        "#;

        engine.load_enemy_script_from_str("grunt", script).unwrap();

        let stats = engine.get_enemy_stats("grunt").unwrap();
        assert_eq!(stats.health, 20);
        assert_eq!(stats.points, 50);
    }
}
