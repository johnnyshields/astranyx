// World 1: Space Station Alpha
// A multi-segment stage with classic shmup gameplay transitioning to FPS.

const WORLD = #{
    id: "station",
    name: "Space Station Alpha",
    description: "Infiltrate the enemy space station",
    start_segment: "1_approach",
    music: "stage1_theme",
    skybox: "space_nebula",
};

fn get_world() { WORLD }
