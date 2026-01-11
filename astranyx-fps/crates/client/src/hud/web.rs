//! WASM HUD implementation using web-sys 2D Canvas.

use wasm_bindgen::JsCast;
use web_sys::{CanvasRenderingContext2d, HtmlCanvasElement};

use super::{Hud, HudGameState, HudPlayerState, WeaponSlot};

/// Web-based HUD using HTML Canvas 2D.
pub struct WebHud {
    canvas: Option<HtmlCanvasElement>,
    ctx: Option<CanvasRenderingContext2d>,
    width: u32,
    height: u32,

    // Viewport matching WebGL's 5:3 letterbox/pillarbox
    viewport_x: f64,
    viewport_y: f64,
    viewport_width: f64,
    viewport_height: f64,

    // Design resolution
    design_width: f64,
    design_height: f64,
}

impl Default for WebHud {
    fn default() -> Self {
        Self::new()
    }
}

impl WebHud {
    pub fn new() -> Self {
        Self {
            canvas: None,
            ctx: None,
            width: 0,
            height: 0,
            viewport_x: 0.0,
            viewport_y: 0.0,
            viewport_width: 0.0,
            viewport_height: 0.0,
            design_width: 1000.0,
            design_height: 600.0,
        }
    }

    /// Convert design coordinates to screen coordinates.
    /// Design space: -500 to +500 X, -300 to +300 Y (origin center)
    fn to_screen(&self, x: f64, y: f64) -> (f64, f64) {
        let scale_x = self.viewport_width / self.design_width;
        let scale_y = self.viewport_height / self.design_height;

        (
            self.viewport_x + (x + self.design_width / 2.0) * scale_x,
            self.viewport_y + (self.design_height / 2.0 - y) * scale_y,
        )
    }

    /// Get scale factor for consistent sizing.
    fn get_scale(&self) -> f64 {
        self.viewport_width / self.design_width
    }

    fn draw_rect(&self, x: f64, y: f64, w: f64, h: f64, color: &str) {
        let ctx: &CanvasRenderingContext2d = match &self.ctx {
            Some(c) => c,
            None => return,
        };
        let (sx, sy) = self.to_screen(x, y);
        let scale = self.get_scale();
        ctx.set_fill_style_str(color);
        ctx.fill_rect(sx - (w * scale) / 2.0, sy - (h * scale) / 2.0, w * scale, h * scale);
    }

    fn draw_rect_outline(&self, x: f64, y: f64, w: f64, h: f64, color: &str, line_width: f64) {
        let ctx: &CanvasRenderingContext2d = match &self.ctx {
            Some(c) => c,
            None => return,
        };
        let (sx, sy) = self.to_screen(x, y);
        let scale = self.get_scale();
        ctx.set_stroke_style_str(color);
        ctx.set_line_width(line_width * scale);
        ctx.stroke_rect(sx - (w * scale) / 2.0, sy - (h * scale) / 2.0, w * scale, h * scale);
    }

    fn draw_text(&self, text: &str, x: f64, y: f64, size: f64, color: &str, align: &str) {
        let ctx: &CanvasRenderingContext2d = match &self.ctx {
            Some(c) => c,
            None => return,
        };
        let (sx, sy) = self.to_screen(x, y);
        let scale = self.get_scale();
        let font_size = (size * scale).round() as i32;

        ctx.set_font(&format!("{}px 'Courier New', monospace", font_size));
        ctx.set_text_align(align);
        ctx.set_text_baseline("middle");

        // Outline
        ctx.set_stroke_style_str("#000");
        ctx.set_line_width(3.0 * scale);
        ctx.set_line_join("round");
        let _ = ctx.stroke_text(text, sx, sy);

        // Fill
        ctx.set_fill_style_str(color);
        let _ = ctx.fill_text(text, sx, sy);
    }
}

impl Hud for WebHud {
    fn init(&mut self) {
        // Create HUD canvas
        let window = match web_sys::window() {
            Some(w) => w,
            None => return,
        };
        let document = match window.document() {
            Some(d) => d,
            None => return,
        };

        // Check if canvas already exists
        if let Some(existing) = document.get_element_by_id("hud-canvas") {
            if let Ok(canvas) = existing.dyn_into::<HtmlCanvasElement>() {
                let ctx = canvas
                    .get_context("2d")
                    .ok()
                    .flatten()
                    .and_then(|c| c.dyn_into::<CanvasRenderingContext2d>().ok());
                self.canvas = Some(canvas);
                self.ctx = ctx;
                return;
            }
        }

        // Create new canvas
        let canvas = match document.create_element("canvas") {
            Ok(e) => match e.dyn_into::<HtmlCanvasElement>() {
                Ok(c) => c,
                Err(_) => return,
            },
            Err(_) => return,
        };

        canvas.set_id("hud-canvas");
        let _ = canvas.style().set_property("position", "absolute");
        let _ = canvas.style().set_property("top", "0");
        let _ = canvas.style().set_property("left", "0");
        let _ = canvas.style().set_property("width", "100%");
        let _ = canvas.style().set_property("height", "100%");
        let _ = canvas.style().set_property("pointer-events", "none");
        let _ = canvas.style().set_property("z-index", "10");

        // Insert into game container
        if let Some(container) = document.get_element_by_id("game-container") {
            let _ = container.append_child(&canvas);
        } else if let Some(body) = document.body() {
            let _ = body.append_child(&canvas);
        }

        let ctx: Option<CanvasRenderingContext2d> = canvas
            .get_context("2d")
            .ok()
            .flatten()
            .and_then(|c| c.dyn_into::<CanvasRenderingContext2d>().ok());

        if let Some(ref c) = ctx {
            c.set_image_smoothing_enabled(false);
        }

        self.canvas = Some(canvas);
        self.ctx = ctx;
    }

    fn resize(&mut self, width: u32, height: u32) {
        self.width = width;
        self.height = height;

        if let Some(canvas) = &self.canvas {
            // Account for devicePixelRatio
            let dpr = web_sys::window()
                .map(|w| w.device_pixel_ratio())
                .unwrap_or(1.0);

            canvas.set_width((width as f64 * dpr) as u32);
            canvas.set_height((height as f64 * dpr) as u32);

            if let Some(c) = &self.ctx {
                let ctx: &CanvasRenderingContext2d = c;
                // Scale context to match CSS pixels
                let _ = ctx.set_transform(dpr, 0.0, 0.0, dpr, 0.0, 0.0);
                ctx.set_image_smoothing_enabled(false);
            }
        }

        // Calculate 5:3 viewport
        let target_aspect = 5.0 / 3.0;
        let screen_aspect = width as f64 / height as f64;

        if screen_aspect > target_aspect {
            // Pillarbox
            self.viewport_height = height as f64;
            self.viewport_width = (height as f64 * target_aspect).floor();
            self.viewport_x = ((width as f64 - self.viewport_width) / 2.0).floor();
            self.viewport_y = 0.0;
        } else {
            // Letterbox
            self.viewport_width = width as f64;
            self.viewport_height = (width as f64 / target_aspect).floor();
            self.viewport_x = 0.0;
            self.viewport_y = ((height as f64 - self.viewport_height) / 2.0).floor();
        }
    }

    fn clear(&mut self) {
        let ctx: &CanvasRenderingContext2d = match &self.ctx {
            Some(c) => c,
            None => return,
        };
        ctx.clear_rect(0.0, 0.0, self.width as f64, self.height as f64);
    }

    fn render_player_state(&mut self, state: &HudPlayerState) {
        // Shield bar (top-left)
        let shield_x = -400.0;
        let shield_y = 250.0;

        // Background
        self.draw_rect(shield_x, shield_y, 154.0, 18.0, "rgba(20, 20, 30, 0.9)");
        // Border
        self.draw_rect_outline(shield_x, shield_y, 152.0, 16.0, "rgba(0, 128, 128, 0.8)", 2.0);
        // Fill
        let shield_ratio = state.shields / state.max_shields.max(1.0);
        let shield_color = if shield_ratio > 0.25 { "#0f8" } else { "#f43" };
        let shield_width = 148.0 * shield_ratio as f64;
        self.draw_rect(
            shield_x - (148.0 - shield_width) / 2.0,
            shield_y,
            shield_width,
            12.0,
            shield_color,
        );
        // Label
        self.draw_text("SHIELD", shield_x - 60.0, shield_y, 10.0, "#fff", "right");

        // Lives (below shield)
        let lives_y = 225.0;
        self.draw_text("LIVES", -475.0, lives_y, 10.0, "#fff", "left");
        for i in 0..state.lives {
            self.draw_rect(-420.0 + i as f64 * 20.0, lives_y, 14.0, 14.0, "#f55");
        }

        // Ship level
        let level_y = 200.0;
        self.draw_text("LEVEL", -475.0, level_y, 10.0, "#fff", "left");
        for i in 0..state.ship_level {
            self.draw_rect(-420.0 + i as f64 * 16.0, level_y, 12.0, 12.0, "#ff0");
        }
    }

    fn render_game_state(&mut self, state: &HudGameState) {
        // Score would come from player state, but we need it passed in game state too
        // For now, skip score display in this method

        // Boss health bar (top center when active)
        if state.boss_active && state.boss_max_health > 0.0 {
            let bar_x = 0.0;
            let bar_y = 260.0;
            let bar_width = 300.0;
            let bar_height = 20.0;

            // Background
            self.draw_rect(bar_x, bar_y, bar_width + 4.0, bar_height + 4.0, "rgba(60, 0, 0, 0.9)");
            // Border
            self.draw_rect_outline(bar_x, bar_y, bar_width + 2.0, bar_height + 2.0, "#f00", 2.0);
            // Health fill
            let health_ratio = (state.boss_health / state.boss_max_health).clamp(0.0, 1.0);
            let health_width = bar_width * health_ratio as f64;
            self.draw_rect(
                bar_x - (bar_width - health_width) / 2.0,
                bar_y,
                health_width,
                bar_height - 4.0,
                "#f00",
            );
            // Label
            self.draw_text("WARNING", bar_x, bar_y + 25.0, 12.0, "#f00", "center");
        }
    }

    fn render_weapon_slots(&mut self, slots: &[WeaponSlot], active_index: usize) {
        let slot_start_x = -420.0;
        let slot_y = 140.0;
        let slot_width = 70.0;
        let slot_height = 35.0;
        let slot_gap = 10.0;

        for (i, slot) in slots.iter().enumerate() {
            let slot_x = slot_start_x + i as f64 * (slot_width + slot_gap);
            let is_active = i == active_index;

            // Slot background
            self.draw_rect(slot_x, slot_y, slot_width + 2.0, slot_height + 2.0, "rgba(20, 20, 30, 0.9)");

            // Active indicator
            if is_active {
                self.draw_rect_outline(slot_x, slot_y, slot_width, slot_height, "#fff", 2.0);
            }

            // Weapon name
            let color = format!(
                "rgba({}, {}, {}, {})",
                (slot.color[0] * 255.0) as u8,
                (slot.color[1] * 255.0) as u8,
                (slot.color[2] * 255.0) as u8,
                slot.color[3]
            );
            self.draw_text(&slot.name, slot_x, slot_y + 6.0, 11.0, &color, "center");

            // Ammo bar
            self.draw_rect(slot_x, slot_y - 10.0, slot_width - 6.0, 8.0, "rgba(40, 40, 50, 0.9)");
            let ammo_ratio = slot.ammo as f64 / slot.max_ammo.max(1) as f64;
            let ammo_bar_width = (slot_width - 6.0) * ammo_ratio;
            if ammo_bar_width > 0.0 {
                self.draw_rect(
                    slot_x - ((slot_width - 6.0) - ammo_bar_width) / 2.0,
                    slot_y - 10.0,
                    ammo_bar_width,
                    6.0,
                    &color,
                );
            }

            // Ammo count
            self.draw_text(&slot.ammo.to_string(), slot_x, slot_y - 10.0, 8.0, "#fff", "center");
        }
    }

    fn render_health_bar(&mut self, screen_x: f32, screen_y: f32, health: f32, max_health: f32, width: f32) {
        let scale = self.get_scale();
        let bar_width = width as f64 * scale;
        let bar_height = 6.0 * scale;

        // Convert from world-projected coords to canvas
        let x = self.viewport_x + (screen_x as f64 + self.design_width / 2.0) * (self.viewport_width / self.design_width);
        let y = self.viewport_y + (self.design_height / 2.0 - screen_y as f64) * (self.viewport_height / self.design_height);

        let health_ratio = (health / max_health.max(1.0)).clamp(0.0, 1.0);
        let fill_width = bar_width * health_ratio as f64;

        let health_color = if health_ratio > 0.6 {
            "#0f0"
        } else if health_ratio > 0.3 {
            "#ff0"
        } else {
            "#f00"
        };

        let ctx: &CanvasRenderingContext2d = match &self.ctx {
            Some(c) => c,
            None => return,
        };
        // Background
        ctx.set_fill_style_str("rgba(30, 30, 30, 0.8)");
        ctx.fill_rect(x - bar_width / 2.0 - 2.0, y - bar_height / 2.0 - 2.0, bar_width + 4.0, bar_height + 4.0);

        // Health fill
        ctx.set_fill_style_str(health_color);
        ctx.fill_rect(x - bar_width / 2.0, y - bar_height / 2.0, fill_width, bar_height);
    }

    fn render_weapon_label(&mut self, screen_x: f32, screen_y: f32, name: &str, color: [f32; 4]) {
        let ctx: &CanvasRenderingContext2d = match &self.ctx {
            Some(c) => c,
            None => return,
        };

        let scale = self.get_scale();

        // Convert from world-projected coords to canvas
        let x = self.viewport_x + (screen_x as f64 + self.design_width / 2.0) * (self.viewport_width / self.design_width);
        let y = self.viewport_y + (self.design_height / 2.0 - screen_y as f64) * (self.viewport_height / self.design_height);

        let text_width = name.len() as f64 * 8.0 * scale + 12.0 * scale;
        let text_height = 18.0 * scale;

        // Background pill
        ctx.set_fill_style_str("rgba(15, 15, 25, 0.9)");
        ctx.begin_path();
        let r = 4.0 * scale;
        ctx.move_to(x - text_width / 2.0 + r, y - text_height / 2.0);
        ctx.line_to(x + text_width / 2.0 - r, y - text_height / 2.0);
        ctx.quadratic_curve_to(x + text_width / 2.0, y - text_height / 2.0, x + text_width / 2.0, y - text_height / 2.0 + r);
        ctx.line_to(x + text_width / 2.0, y + text_height / 2.0 - r);
        ctx.quadratic_curve_to(x + text_width / 2.0, y + text_height / 2.0, x + text_width / 2.0 - r, y + text_height / 2.0);
        ctx.line_to(x - text_width / 2.0 + r, y + text_height / 2.0);
        ctx.quadratic_curve_to(x - text_width / 2.0, y + text_height / 2.0, x - text_width / 2.0, y + text_height / 2.0 - r);
        ctx.line_to(x - text_width / 2.0, y - text_height / 2.0 + r);
        ctx.quadratic_curve_to(x - text_width / 2.0, y - text_height / 2.0, x - text_width / 2.0 + r, y - text_height / 2.0);
        ctx.close_path();
        ctx.fill();

        // Color indicator bar
        let color_str = format!(
            "rgba({}, {}, {}, {})",
            (color[0] * 255.0) as u8,
            (color[1] * 255.0) as u8,
            (color[2] * 255.0) as u8,
            color[3]
        );
        ctx.set_fill_style_str(&color_str);
        ctx.fill_rect(
            x - text_width / 2.0 + 2.0 * scale,
            y + text_height / 2.0 - 4.0 * scale,
            text_width - 4.0 * scale,
            2.0 * scale,
        );

        // Weapon name
        let font_size = (11.0 * scale).round() as i32;
        ctx.set_font(&format!("{}px 'Courier New', monospace", font_size));
        ctx.set_text_align("center");
        ctx.set_text_baseline("middle");

        ctx.set_stroke_style_str("#000");
        ctx.set_line_width(3.0 * scale);
        ctx.set_line_join("round");
        let _ = ctx.stroke_text(name, x, y - 1.0 * scale);

        ctx.set_fill_style_str("#fff");
        let _ = ctx.fill_text(name, x, y - 1.0 * scale);
    }
}
