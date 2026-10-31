// ============================================================
// SANCTUM OF THE FIRSTS — Phase 2: Tower Defense Engine & Combat
// ============================================================
(function () {
  'use strict';

  // ========================================================
  // CONFIGURATION & CONSTANTS
  // ========================================================
  const GRID = 16;
  const PIXEL_SCALE = 2; // Crisp retro pixel-crunch

  // Color Palette
  const C = {
    // Sandstone strata
    SAND_L:   0xF0C050, // Sunlit golden sandstone
    SAND_M:   0xE59838, // Warm desert ochre
    SAND_D:   0xC87A28, // Terracotta shade
    SAND_X:   0xAA5B1A, // Deep cliff rock
    BED_1:    0x633512, // Diorama plinth stratum 1
    BED_2:    0x401E06, // Diorama plinth stratum 2
    BED_3:    0x220F03, // Diorama plinth base

    // Cobblestone path
    COB_L:    0x968B7C,
    COB_D:    0x6D6355,
    COB_CURB: 0x524B40,

    // Water & Foam
    WAT_FOAM: 0xFFFFFF,
    WAT_L:    0x4DC3FF,
    WAT_M:    0x2088DE,
    WAT_D:    0x1258A2,

    // Vegetation
    CACT:     0x1D8A48,
    CACT_D:   0x136534,
    CACT_FL:  0xFF3366,
    MOSS:     0x4E8A32,
    MOSS_DK:  0x356320,
    FLOWER_Y: 0xFFD830,

    // Vegetation & Environment Palette Extensions
    CACT_RIB:        0x1B7A43, // Deep ribbed saguaro green
    PRICKLY_PAD:     0x2E8B57, // Rounded prickly pear dome pad
    WOOD_ACACIA:     0x8B5A2B, // Sun-bleached acacia branches
    WOOD_ACACIA_DK:  0x5C3A21, // Gnarled dark acacia trunk
    TUMBLE_TWIG:     0xC29B38, // Dried yellow-brown twig scrub
    HOODOO_RED:      0xA0522D, // Deep terracotta hoodoo stratum
    BONE_IVORY:      0xE8E0D5, // Prehistoric weathered beast ivory
    BONE_DK:         0xC8BFAF, // Fossil/bone socket shadow
    TERRACOTTA:      0xCD5C5C, // Clay pottery urns and shards
    TERRA_RIM:       0xDE7A60, // Urn rim/neck terracotta highlight
    RUIN_ARCH:       0xA39E93, // Weathered ancient stone arch
    REED_BROWN:      0x8B4513, // Oasis cattail brown reed heads

    // Sanctum stone
    STN_L:    0xB4A89A,
    STN_M:    0x928678,
    STN_D:    0x6E6356,
    STN_X:    0x483F36,
    GLOW_GRN: 0x39FF14, // Primal emerald glow
    GLOW_RED: 0xFF1744, // Angry breached glow

    // Pedestal
    PED_BASE: 0x827D75,
    PED_TOP:  0x5A544C,
    PED_RUNE: 0x39FF14,

    // Stone Golem
    SG_L:     0xA4A8AB,
    SG_M:     0x7A7E82,
    SG_D:     0x585B5F,
    SG_DK:    0x3A3C3E,

    // Oak Golem
    OG_TAN:   0xDEBD8C,
    OG_WD:    0x7E4C1D,
    OG_WD_DK: 0x54300F,
    OG_MTL:   0x4A4D50,

    // Brick Golem
    BG_BR:    0xA84A32,
    BG_BR_DK: 0x803320,
    BG_SL:    0x2A3335,
    BG_SL_DK: 0x1A2122,

    // Diorite Golem
    DG_W:     0xF6F8FA,
    DG_G:     0xD4DAE0,
    DG_GDK:   0x9DA4AD,
    DG_GLD:   0xFFC826,
    DG_GDK_G: 0xD89E10,

    // Alien Invaders Palette (Cosmic Void Theme)
    AL_ALLOY:    0x3B1E54, // Dark alien alloy
    AL_OBSID:    0x140D22, // Obsidian void carapace
    AL_VOID_DK:  0x0F0A18, // Deep abyss black-violet
    AL_VOID_M:   0x221338, // Amethyst shadow chitin
    AL_CHITIN_D: 0x48195E, // Royal purple dorsal carapace
    AL_CHITIN_L: 0x732891, // Iridescent purple highlights
    AL_BELLY:    0x2E1A46, // Ribbed underbelly plates
    AL_CYAN_NEON:0x00F5D4, // Glowing electric cyan
    AL_CYAN_BRT: 0x80FFF0, // High-energy cyan visor/spores
    AL_MAG_NEON: 0xFF007F, // Bioluminescent plasma magenta
    AL_MAG_BRT:  0xFF66B2, // Brilliant neon pink core
    AL_ACID:     0x76FF03, // Toxic bio-plasma lime
    AL_GOLD_ARM: 0xFFB300, // Armored carapace amber/gold

    SKY:         0x16120D,
  };

  // Dynamic Procedural Terrain & Path State
  var WAYPOINTS = [];
  var PATH_TILES = [];
  var pathSet = new Set();
  var PEDESTAL_CONFIGS = [];
  var heightMap = new Map(); // key: `${x},${z}` => elevation height
  var startingPortalGroup = null;
  var islandRootObjects = []; // Track root objects of starting island for complete level teardown/regeneration

  // Grid Registries for Dynamic Path-First Carving & Obstacle Evacuation
  var terrainMeshesByCell = new Map(); // `${x},${z}` => Array<THREE.Mesh>
  var decorByCell = new Map();         // `${x},${z}` => Array<THREE.Object3D>
  var pathMeshesByCell = new Map();    // `${x},${z}` => Array<THREE.Mesh>
  var carvedConnectorMeshes = [];      // Track dynamically carved connector meshes

  // 4-Connected Segment Pathfinder using A* Manhattan distance
  function find4ConnectedSegment(x1, z1, x2, z2, minX, maxX, minZ, maxZ, forbiddenSet = null) {
    if (x1 === x2 && z1 === z2) return [[x1, z1]];
    const queue = [{ x: x1, z: z1, path: [[x1, z1]] }];
    const visited = new Set([`${x1},${z1}`]);

    const DIRS = [
      { dx: 1, dz: 0 },
      { dx: -1, dz: 0 },
      { dx: 0, dz: 1 },
      { dx: 0, dz: -1 }
    ];

    while (queue.length > 0) {
      queue.sort((a, b) => {
        const d1 = Math.abs(a.x - x2) + Math.abs(a.z - z2);
        const d2 = Math.abs(b.x - x2) + Math.abs(b.z - z2);
        return (a.path.length + d1) - (b.path.length + d2);
      });

      const cur = queue.shift();
      if (cur.x === x2 && cur.z === z2) {
        return cur.path;
      }

      if (cur.path.length > 60) continue;

      for (const d of DIRS) {
        const nx = cur.x + d.dx;
        const nz = cur.z + d.dz;
        if (nx < minX || nx > maxX || nz < minZ || nz > maxZ) continue;
        const nk = `${nx},${nz}`;
        if (visited.has(nk)) continue;
        if (forbiddenSet && forbiddenSet.has(nk) && !(nx === x2 && nz === z2)) continue;

        visited.add(nk);
        queue.push({
          x: nx,
          z: nz,
          path: [...cur.path, [nx, nz]]
        });
      }
    }

    // Direct Manhattan fallback
    const fallback = [[x1, z1]];
    let cx = x1, cz = z1;
    while (cx !== x2 || cz !== z2) {
      const dx = x2 - cx;
      const dz = z2 - cz;
      if (dx !== 0 && dz !== 0) {
        if (Math.abs(dx) >= Math.abs(dz)) cx += Math.sign(dx);
        else cz += Math.sign(dz);
      } else if (dx !== 0) {
        cx += Math.sign(dx);
      } else if (dz !== 0) {
        cz += Math.sign(dz);
      }
      fallback.push([cx, cz]);
    }
    return fallback;
  }

  // Guaranteed Contiguous 4-Connected Grid Path Generator (Zero Gaps, Zero Missing Tiles!)
  function generateContiguousGridPath(startX, startZ, endX, endZ, minX, maxX, minZ, maxZ, chicanes = [], forbiddenSet = null) {
    const fullPath = [];
    const visited = new Set();
    const targets = [{ x: startX, z: startZ }, ...chicanes, { x: endX, z: endZ }];

    for (let t = 0; t < targets.length - 1; t++) {
      const p1 = targets[t];
      const p2 = targets[t + 1];
      const seg = find4ConnectedSegment(p1.x, p1.z, p2.x, p2.z, minX, maxX, minZ, maxZ, forbiddenSet);
      seg.forEach(pt => {
        const k = `${pt[0]},${pt[1]}`;
        if (!visited.has(k)) {
          visited.add(k);
          fullPath.push(pt);
        }
      });
    }

    return fullPath;
  }

  // ========================================================
  // REUSABLE PROCEDURAL TERRAIN ASSET LIBRARY
  // ========================================================
  const TerrainAssetLibrary = {
    // --------------------------------------------------------
    // CATEGORY A: FLORA & DESERT VEGETATION
    // --------------------------------------------------------

    // 1. Saguaro Cactus (Ribbed multi-armed saguaro with flower buds)
    spawnSaguaro: function (parent, x, y, z, h = 3, armStyle = 1) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'saguaro';

      // Ribbed vertical column
      for (let i = 0; i < h; i++) {
        const col = (i % 2 === 0) ? C.CACT_RIB : C.CACT_D;
        vox(0, i * 0.42 + 0.21, 0, 0.34, 0.42, 0.34, col, g);
      }
      // Top flower bud
      vox(0, h * 0.42 + 0.10, 0, 0.18, 0.14, 0.18, C.CACT_FL, g, C.CACT_FL, 0.8);

      // Arm 1 (Left bough)
      if (armStyle >= 1 && h >= 3) {
        vox(-0.28, 0.65, 0, 0.28, 0.18, 0.22, C.CACT_RIB, g);
        vox(-0.42, 0.95, 0, 0.20, 0.48, 0.20, C.CACT_D, g);
        vox(-0.42, 1.23, 0, 0.14, 0.10, 0.14, C.CACT_FL, g, C.CACT_FL, 0.7);
      }
      // Arm 2 (Right bough, higher)
      if (armStyle >= 2 && h >= 4) {
        vox(0.28, 1.05, 0, 0.28, 0.18, 0.22, C.CACT_RIB, g);
        vox(0.42, 1.40, 0, 0.20, 0.58, 0.20, C.CACT_D, g);
        vox(0.42, 1.73, 0, 0.14, 0.10, 0.14, C.CACT_FL, g, C.CACT_FL, 0.7);
      }

      environmentalProps.push(g);

      if (parent) parent.add(g);
      return g;
    },

    // 2. Prickly Pear Cactus (Asymmetrical dome pads with magenta/yellow buds)
    spawnPricklyPear: function (parent, x, y, z) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'prickly_pear';

      // Base grounding pad
      vox(0, 0.14, 0, 0.44, 0.26, 0.24, C.CACT_RIB, g);
      // Left angled pad
      vox(-0.24, 0.28, 0.04, 0.32, 0.24, 0.20, C.PRICKLY_PAD, g);
      // Right angled pad
      vox(0.20, 0.32, -0.04, 0.34, 0.28, 0.20, C.CACT_RIB, g);
      // Center upper pad
      vox(-0.04, 0.46, 0.02, 0.30, 0.24, 0.18, C.PRICKLY_PAD, g);
      // Side offset pad
      vox(0.34, 0.50, 0.06, 0.20, 0.18, 0.15, C.CACT_RIB, g);
      // Buds (Magenta & Yellow)
      vox(-0.04, 0.62, 0.02, 0.13, 0.11, 0.13, C.CACT_FL, g, C.CACT_FL, 0.8);
      vox(0.34, 0.64, 0.06, 0.11, 0.09, 0.11, C.FLOWER_Y, g, C.FLOWER_Y, 0.8);
      vox(-0.24, 0.43, 0.04, 0.11, 0.09, 0.11, C.FLOWER_Y, g, C.FLOWER_Y, 0.5);

      environmentalProps.push(g);

      if (parent) parent.add(g);
      return g;
    },

    // 3. Acacia Tree (Sun-bleached gnarled wood, flat twisting canopy)
    spawnAcaciaTree: function (parent, x, y, z) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'acacia_tree';

      // Base trunk
      vox(0, 0.35, 0, 0.26, 0.70, 0.26, C.WOOD_ACACIA_DK, g);
      // Twisted mid-trunk
      vox(0.12, 0.95, 0.06, 0.22, 0.60, 0.22, C.WOOD_ACACIA, g);

      // Separate canopy group anchored at upper trunk for natural wind swaying
      const canopy = new THREE.Group();
      canopy.position.set(0.24, 1.45, 0.10);
      vox(0, 0, 0, 0.20, 0.50, 0.20, C.WOOD_ACACIA_DK, canopy);
      vox(-0.40, 0.31, -0.16, 0.52, 0.15, 0.18, C.WOOD_ACACIA, canopy);
      vox( 0.28, 0.35,  0.08, 0.50, 0.15, 0.18, C.WOOD_ACACIA, canopy);
      vox(-0.12, 0.57,  0.16, 0.16, 0.30, 0.32, C.WOOD_ACACIA_DK, canopy);
      vox(-0.58, 0.47, -0.20, 0.65, 0.10, 0.55, 0x556B2F, canopy);
      vox(-0.02, 0.67,  0.02, 0.80, 0.10, 0.70, 0x556B2F, canopy);
      vox( 0.46, 0.51,  0.16, 0.55, 0.10, 0.50, 0x556B2F, canopy);
      vox(-0.22, 0.75, -0.06, 0.40, 0.08, 0.40, 0x6B8E23, canopy);

      g.add(canopy);
      g.userData.canopyGroup = canopy;
      environmentalProps.push(g);

      if (parent) parent.add(g);
      return g;
    },

    // 3b. Desert Flora Cluster (Multi-tile footprint: 2x1 mature acacia tree with shaded prickly pear & tumbleweed)
    spawnDesertFloraCluster: function (parent, x, y, z, width = 2, depth = 1) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'flora_cluster';
      g.userData.width = width;
      g.userData.depth = depth;

      // Tile 0: Gnarled Acacia Tree
      vox(0, 0.35, 0, 0.26, 0.70, 0.26, C.WOOD_ACACIA_DK, g);
      vox(0.12, 0.95, 0.06, 0.22, 0.60, 0.22, C.WOOD_ACACIA, g);

      const canopy = new THREE.Group();
      canopy.position.set(0.24, 1.45, 0.10);
      vox(0, 0, 0, 0.20, 0.50, 0.20, C.WOOD_ACACIA_DK, canopy);
      vox(-0.40, 0.31, -0.16, 0.52, 0.15, 0.18, C.WOOD_ACACIA, canopy);
      vox( 0.28, 0.35,  0.08, 0.50, 0.15, 0.18, C.WOOD_ACACIA, canopy);
      vox(-0.12, 0.57,  0.16, 0.16, 0.30, 0.32, C.WOOD_ACACIA_DK, canopy);
      vox(-0.58, 0.47, -0.20, 0.65, 0.10, 0.55, 0x556B2F, canopy);
      vox(-0.02, 0.67,  0.02, 0.80, 0.10, 0.70, 0x556B2F, canopy);
      vox( 0.46, 0.51,  0.16, 0.55, 0.10, 0.50, 0x556B2F, canopy);
      vox(-0.22, 0.75, -0.06, 0.40, 0.08, 0.40, 0x6B8E23, canopy);
      g.add(canopy);
      g.userData.canopyGroup = canopy;

      // Tile 1: Nestled in tree shade: Prickly Pear Cactus & Tumbleweed
      const px = 1.0, pz = 0.0;
      vox(px, 0.14, pz, 0.40, 0.24, 0.22, C.CACT_RIB, g);
      vox(px - 0.20, 0.28, pz + 0.04, 0.28, 0.22, 0.18, C.PRICKLY_PAD, g);
      vox(px + 0.18, 0.30, pz - 0.04, 0.30, 0.24, 0.18, C.CACT_RIB, g);
      vox(px - 0.04, 0.44, pz + 0.02, 0.26, 0.20, 0.16, C.PRICKLY_PAD, g);
      vox(px - 0.04, 0.58, pz + 0.02, 0.12, 0.10, 0.12, C.CACT_FL, g, C.CACT_FL, 0.8);
      vox(px + 0.18, 0.45, pz - 0.04, 0.10, 0.08, 0.10, C.FLOWER_Y, g, C.FLOWER_Y, 0.8);

      // Dried tumbleweed resting in shadow
      vox(px + 0.32, 0.12, pz + 0.24, 0.24, 0.22, 0.24, C.TUMBLE_TWIG, g);
      vox(px + 0.38, 0.15, pz + 0.20, 0.16, 0.18, 0.16, 0xA07828, g);

      // Sandstone grounding slab
      vox(0.5, 0.04, 0.1, 0.65, 0.08, 0.50, C.SAND_M, g);

      environmentalProps.push(g);

      if (parent) parent.add(g);
      return g;
    },

    // 4. Tumbleweed Scrub (Chaotic bundle of dried yellow-brown twig voxels)
    spawnTumbleweedScrub: function (parent, x, y, z) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'tumbleweed';
      g.userData.baseY = y;
      g.userData.baseX = x;

      vox(0, 0.14, 0, 0.30, 0.28, 0.30, C.TUMBLE_TWIG, g);
      vox(0.11, 0.19, -0.07, 0.20, 0.22, 0.22, 0xA07828, g);
      vox(-0.09, 0.15, 0.09, 0.22, 0.20, 0.20, C.TUMBLE_TWIG, g);
      vox(-0.05, 0.28, -0.05, 0.22, 0.15, 0.18, 0x8C6820, g);
      vox(0.07, 0.30, 0.07, 0.18, 0.16, 0.20, C.TUMBLE_TWIG, g);
      vox(0.15, 0.09, 0.11, 0.14, 0.13, 0.14, 0xA07828, g);

      environmentalProps.push(g);

      if (parent) parent.add(g);
      return g;
    },

    // --------------------------------------------------------
    // CATEGORY B: GEOLOGICAL & REMAINS
    // --------------------------------------------------------

    // 5. Hoodoo Mesa (Stratified rock column with warm ochre/terracotta gradients)
    spawnHoodooMesa: function (parent, x, y, z, h = 3) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'hoodoo_mesa';

      // Base plinth
      vox(0, 0.25, 0, 0.82, 0.50, 0.82, C.HOODOO_RED, g);
      // Lower stepped taper
      vox(0.02, 0.65, -0.02, 0.64, 0.40, 0.64, C.SAND_D, g);
      // Narrow neck column
      vox(-0.02, 1.15, 0.02, 0.44, 0.60, 0.44, C.SAND_M, g);
      // Mid-ledge shelf
      vox(0.06, 1.55, 0.0, 0.52, 0.24, 0.48, C.SAND_D, g);
      // Upper neck
      vox(0.0, 1.90, 0.0, 0.40, 0.50, 0.40, C.SAND_M, g);
      // Overhanging capstone ledge
      vox(0.02, 2.25, -0.02, 0.76, 0.24, 0.74, C.HOODOO_RED, g);
      // Capstone crown
      vox(0.0, 2.44, 0.0, 0.56, 0.16, 0.54, C.SAND_D, g);
      // Fallen base rubble rock
      vox(0.44, 0.14, 0.40, 0.28, 0.22, 0.26, C.SAND_M, g);

      if (parent) parent.add(g);
      return g;
    },

    // 5b. Mesa Hoodoo Ridge (Multi-tile footprint: 2x1 stratified sandstone columns joined by rocky saddle)
    spawnMesaHoodooRidge: function (parent, x, y, z, width = 2, depth = 1) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'hoodoo_ridge';
      g.userData.width = width;
      g.userData.depth = depth;

      // Column 1 (Towering main hoodoo at x=0)
      vox(0, 0.28, 0, 0.82, 0.56, 0.82, C.HOODOO_RED, g);
      vox(0, 0.78, 0, 0.66, 0.44, 0.66, C.SAND_D, g);
      vox(0, 1.40, 0, 0.46, 0.80, 0.46, C.SAND_M, g);
      vox(0.04, 1.95, 0, 0.54, 0.30, 0.52, C.SAND_D, g);
      vox(0, 2.45, 0, 0.42, 0.70, 0.42, C.SAND_M, g);
      vox(0, 2.90, 0, 0.78, 0.22, 0.76, C.HOODOO_RED, g);
      vox(0, 3.08, 0, 0.58, 0.14, 0.56, C.SAND_D, g);

      // Connecting rocky talus saddle spine
      vox(0.5, 0.35, 0, 0.60, 0.70, 0.60, C.HOODOO_RED, g);
      vox(0.5, 0.75, 0.05, 0.44, 0.32, 0.46, C.SAND_D, g);

      // Column 2 (Secondary stepped column at x=1)
      vox(1.0, 0.24, 0, 0.76, 0.48, 0.76, C.HOODOO_RED, g);
      vox(1.0, 0.68, 0, 0.60, 0.40, 0.60, C.SAND_D, g);
      vox(1.0, 1.18, 0, 0.44, 0.60, 0.44, C.SAND_M, g);
      vox(1.0, 1.62, 0, 0.68, 0.20, 0.66, C.HOODOO_RED, g);
      vox(1.0, 1.78, 0, 0.50, 0.12, 0.50, C.SAND_D, g);

      // Base scree boulders
      vox(0.40, 0.12,  0.35, 0.28, 0.20, 0.26, C.SAND_M, g);
      vox(1.30, 0.10, -0.28, 0.24, 0.16, 0.22, C.SAND_X, g);

      environmentalProps.push(g);

      if (parent) parent.add(g);
      return g;
    },

    // 6. Boulder Pile (Asymmetric cluster of tumbled rocks & gravel)
    spawnBoulderPile: function (parent, x, y, z) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'boulder_pile';

      // Main angled boulder
      vox(-0.08, 0.28, 0.04, 0.66, 0.54, 0.60, C.SAND_D, g);
      // Resting rock
      vox(0.30, 0.18, -0.12, 0.48, 0.38, 0.44, C.SAND_M, g);
      // Stacked top rock
      vox(-0.04, 0.62, 0.08, 0.38, 0.26, 0.36, C.SAND_X, g);
      // Low wedge rock
      vox(0.16, 0.13, 0.28, 0.34, 0.24, 0.32, C.STN_D, g);
      // Gravel slab 1
      vox(-0.38, 0.07, -0.18, 0.22, 0.12, 0.24, C.SAND_X, g);
      // Gravel slab 2
      vox(0.42, 0.07, 0.14, 0.20, 0.11, 0.20, C.SAND_M, g);

      if (parent) parent.add(g);
      return g;
    },

    // 7. Fossil Ribcage (Massive prehistoric beast arched ribs protruding from sand)
    spawnFossilRibcage: function (parent, x, y, z) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'fossil_ribcage';

      // Buried vertebral column
      vox(0, 0.10, 0, 0.22, 0.20, 1.10, C.BONE_DK, g);
      // Rib Pair 1 (Anterior)
      vox(-0.32, 0.36, -0.34, 0.12, 0.52, 0.12, C.BONE_IVORY, g);
      vox(-0.18, 0.64, -0.34, 0.20, 0.12, 0.12, C.BONE_IVORY, g);
      vox( 0.32, 0.40, -0.34, 0.12, 0.58, 0.12, C.BONE_IVORY, g);
      vox( 0.18, 0.70, -0.34, 0.20, 0.12, 0.12, C.BONE_IVORY, g);
      // Rib Pair 2 (Taller Main Arch)
      vox(-0.38, 0.46, 0.04, 0.14, 0.72, 0.14, C.BONE_IVORY, g);
      vox(-0.20, 0.84, 0.04, 0.26, 0.14, 0.14, C.BONE_IVORY, g);
      vox( 0.38, 0.44, 0.04, 0.14, 0.70, 0.14, C.BONE_IVORY, g);
      vox( 0.20, 0.82, 0.04, 0.26, 0.14, 0.14, C.BONE_IVORY, g);
      // Rib Pair 3 (Posterior Fractured)
      vox(-0.28, 0.26, 0.38, 0.12, 0.38, 0.12, C.BONE_IVORY, g);
      vox( 0.30, 0.34, 0.38, 0.12, 0.50, 0.12, C.BONE_IVORY, g);
      vox( 0.16, 0.60, 0.38, 0.18, 0.12, 0.12, C.BONE_IVORY, g);

      if (parent) parent.add(g);
      return g;
    },

    // 8. Skeleton Remains (Weathered skull and scattered bone dust)
    spawnSkeletonRemains: function (parent, x, y, z) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'skeleton_remains';

      // Skull cranium
      vox(0.08, 0.20, 0.04, 0.32, 0.26, 0.34, C.BONE_IVORY, g);
      // Brow / snout
      vox(0.14, 0.14, 0.18, 0.24, 0.16, 0.14, C.BONE_IVORY, g);
      // Hollow eye sockets band
      vox(0.14, 0.20, 0.24, 0.20, 0.07, 0.05, 0x221A14, g);
      // Half-buried jaw
      vox(0.14, 0.05, 0.20, 0.18, 0.07, 0.10, C.BONE_DK, g);
      // Femur bone shaft
      vox(-0.22, 0.07, -0.12, 0.42, 0.09, 0.10, C.BONE_IVORY, g);
      // Femur condyle knob
      vox(-0.41, 0.09, -0.12, 0.13, 0.13, 0.14, C.BONE_DK, g);
      // Spine vertebra piece
      vox(-0.10, 0.06, 0.28, 0.15, 0.11, 0.15, C.BONE_IVORY, g);
      // Rib sliver
      vox(0.34, 0.07, -0.07, 0.22, 0.07, 0.09, C.BONE_IVORY, g);

      if (parent) parent.add(g);
      return g;
    },

    // --------------------------------------------------------
    // CATEGORY C: WATER & OASIS FEATURES
    // --------------------------------------------------------

    // 9. Oasis Feature (Shallow sunken turquoise pool, cattails & lily pads)
    spawnOasisFeature: function (parent, x, y, z) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'oasis_feature';

      // 1. Sunken basin bed floor (relative y=-0.65, world y=0.35)
      vox(0, -0.65, 0, 0.94, 0.10, 0.94, 0x8C6020, g);
      vox(0, -0.60, 0, 0.88, 0.08, 0.88, 0x6E4A18, g);

      // 2. Sunken turquoise water surface (relative y=-0.32, world y=0.68 -> sunken below y=1 ground)
      const poolW = vox(0, -0.32, 0, 0.82, 0.05, 0.82, C.WAT_M, g, C.WAT_M, 0.35, 0.88);
      poolW.userData.baseY = -0.32;
      oasisWater.push(poolW);

      // 3. Lily pads floating on sunken water surface
      const lp1 = vox(-0.16, -0.29, -0.12, 0.24, 0.02, 0.22, C.PRICKLY_PAD, g);
      lp1.userData.baseY = -0.29;
      lp1.userData.baseRot = 0;
      const lp2 = vox(0.14, -0.29, 0.16, 0.20, 0.02, 0.18, C.MOSS, g);
      lp2.userData.baseY = -0.29;
      lp2.userData.baseRot = 0.5;
      g.userData.lilyPads = [lp1, lp2];

      // 4. Reeds & Cattails rooted in basin floor rising through water
      const reeds = [];
      const r1 = new THREE.Group();
      r1.position.set(0.30, -0.60, -0.24);
      vox(0, 0.36, 0, 0.06, 0.50, 0.06, C.MOSS_DK, r1);
      vox(0, 0.64, 0, 0.10, 0.18, 0.10, C.REED_BROWN, r1);
      g.add(r1);
      reeds.push(r1);

      const r2 = new THREE.Group();
      r2.position.set(0.24, -0.60, -0.30);
      vox(0, 0.32, 0, 0.06, 0.44, 0.06, C.PRICKLY_PAD, r2);
      vox(0, 0.56, 0, 0.09, 0.15, 0.09, C.REED_BROWN, r2);
      g.add(r2);
      reeds.push(r2);

      const r3 = new THREE.Group();
      r3.position.set(-0.28, -0.60, 0.26);
      vox(0, 0.30, 0, 0.06, 0.40, 0.06, C.MOSS_DK, r3);
      vox(0, 0.52, 0, 0.09, 0.14, 0.09, C.REED_BROWN, r3);
      g.add(r3);
      reeds.push(r3);

      g.userData.reeds = reeds;

      // 5. Terraced damp sand rim flush with surrounding y=1 ground
      vox(0, -0.04, -0.46, 0.94, 0.10, 0.10, 0xD49D35, g);
      vox(0, -0.04,  0.46, 0.94, 0.10, 0.10, 0xD49D35, g);
      vox(-0.46, -0.04, 0, 0.10, 0.10, 0.94, 0xD49D35, g);
      vox( 0.46, -0.04, 0, 0.10, 0.10, 0.94, 0xD49D35, g);

      environmentalProps.push(g);
      if (parent) parent.add(g);
      return g;
    },

    // 9b. Grand Oasis Lagoon (Multi-tile footprint: 2x2 or 3x2 sunken pool with lily pads & reeds)
    // NOTE: Palm tree is DETACHED and spawned on dry ground beside the oasis, not inside the water!
    spawnGrandOasis: function (parent, x, y, z, width = 2, depth = 2) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'grand_oasis';
      g.userData.width = width;
      g.userData.depth = depth;

      const cx = (width - 1) * 0.5;
      const cz = (depth - 1) * 0.5;

      // 1. Sunken Basin Excavation Floor (relative y=-0.65, world y=0.35)
      vox(cx, -0.65, cz, width * 0.98, 0.10, depth * 0.98, 0x8C6020, g); // Dark damp clay basin floor
      vox(cx, -0.60, cz, width * 0.90, 0.08, depth * 0.90, 0x6E4A18, g); // Deep silty riverbed

      // 2. Sunken Turquoise Lagoon Water Surface (relative y=-0.30, world y=0.70 -> sunken below y=1 ground)
      const poolW = vox(cx, -0.30, cz, width * 0.88, 0.05, depth * 0.88, C.WAT_M, g, C.WAT_M, 0.35, 0.88);
      poolW.userData.baseY = -0.30;
      oasisWater.push(poolW);

      // Deeper center pool channel
      const deepW = vox(cx, -0.33, cz, (width - 0.6) * 0.65, 0.04, (depth - 0.6) * 0.65, C.WAT_D, g, C.WAT_D, 0.45, 0.92);
      deepW.userData.baseY = -0.33;
      oasisWater.push(deepW);

      // 3. Floating Lily Pads on sunken water surface
      const lilyPads = [];
      const padOffsets = (width >= 3) ? [
        [-0.7, -0.27, -0.2, 0.26, 0.22, C.PRICKLY_PAD, 0],
        [ 0.1, -0.27,  0.3, 0.22, 0.20, C.MOSS, 0.6],
        [ 0.8, -0.27, -0.1, 0.28, 0.24, C.PRICKLY_PAD, 1.2],
        [-0.2, -0.27, -0.3, 0.20, 0.18, C.MOSS, 0.3]
      ] : [
        [-0.25, -0.27, -0.20, 0.28, 0.24, C.PRICKLY_PAD, 0],
        [ 0.25, -0.27,  0.22, 0.24, 0.22, C.MOSS, 0.7],
        [-0.10, -0.27,  0.30, 0.20, 0.18, C.PRICKLY_PAD, 1.4]
      ];

      padOffsets.forEach(([ox, oy, oz, pw, pd, col, rot]) => {
        const lp = vox(cx + ox, oy, cz + oz, pw, 0.02, pd, col, g);
        lp.userData.baseY = oy;
        lp.userData.baseRot = rot;
        lilyPads.push(lp);
      });
      g.userData.lilyPads = lilyPads;

      // 4. Clustered Reeds & Cattails rooted in sunken basin bed rising up through water
      const reeds = [];
      const reedOffsets = [
        [cx - (width * 0.40), cz - (depth * 0.35)],
        [cx - (width * 0.36), cz + (depth * 0.38)],
        [cx + (width * 0.38), cz - (depth * 0.36)],
        [cx - (width * 0.15), cz - (depth * 0.42)],
        [cx + (width * 0.28), cz + (depth * 0.40)]
      ];
      reedOffsets.forEach(([rx, rz], rIdx) => {
        const rg = new THREE.Group();
        rg.position.set(rx, -0.60, rz);
        const stalkH = 0.65 + (rIdx % 3) * 0.12; // Rises from basin bed out of water
        vox(0, stalkH / 2, 0, 0.06, stalkH, 0.06, (rIdx % 2 === 0 ? C.MOSS_DK : C.PRICKLY_PAD), rg);
        vox(0, stalkH + 0.08, 0, 0.09, 0.16, 0.09, C.REED_BROWN, rg);
        g.add(rg);
        reeds.push(rg);
      });
      g.userData.reeds = reeds;

      // 5. Terraced damp sand perimeter rim flush with surrounding y=1 ground
      vox(cx, -0.04, cz - (depth * 0.48), width * 0.98, 0.10, 0.12, 0xD49D35, g);
      vox(cx, -0.04, cz + (depth * 0.48), width * 0.98, 0.10, 0.12, 0xD49D35, g);
      vox(cx - (width * 0.48), -0.04, cz, 0.12, 0.10, depth * 0.98, 0xD49D35, g);
      vox(cx + (width * 0.48), -0.04, cz, 0.12, 0.10, depth * 0.98, 0xD49D35, g);

      environmentalProps.push(g);
      if (parent) parent.add(g);
      return g;
    },

    // --------------------------------------------------------
    // CATEGORY D: ANCIENT SANCTUM RUINS & RELICS
    // --------------------------------------------------------

    // 10. Broken Archway (Weathered stone pillars with collapsed lintel)
    spawnBrokenArchway: function (parent, x, y, z) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'broken_archway';

      // Left Standing Pillar: base, column, capital
      vox(-0.35, 0.18, 0, 0.34, 0.36, 0.34, C.STN_D, g);
      vox(-0.35, 0.65, 0, 0.26, 0.60, 0.26, C.RUIN_ARCH, g);
      vox(-0.35, 1.05, 0, 0.34, 0.22, 0.34, C.STN_L, g);
      // Right Broken Pillar: base, stump
      vox(0.35, 0.18, 0, 0.34, 0.36, 0.34, C.STN_D, g);
      vox(0.35, 0.45, 0, 0.26, 0.30, 0.26, C.RUIN_ARCH, g);
      // Collapsed Arch Lintel (tilted diagonally downward from left capital)
      vox(-0.10, 1.06, 0, 0.34, 0.18, 0.26, C.STN_M, g);
      vox(0.12, 0.86, 0.04, 0.30, 0.18, 0.24, C.RUIN_ARCH, g);
      // Fallen arch stone on ground
      vox(0.36, 0.12, 0.22, 0.24, 0.18, 0.22, C.STN_L, g);
      // Moss growth
      vox(-0.35, 1.18, 0, 0.18, 0.06, 0.18, C.MOSS, g);
      vox(0.32, 0.62, 0, 0.16, 0.05, 0.16, C.MOSS, g);

      if (parent) parent.add(g);
      return g;
    },

    // 10b. Ancient Ruin Colonnade (Multi-tile footprint: 2x2 or 2x1 with standing fluted pillars, collapsed lintel & glowing floor rune)
    spawnAncientRuinColonnade: function (parent, x, y, z, width = 2, depth = 2) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'ancient_ruins';
      g.userData.width = width;
      g.userData.depth = depth;

      const cx = (width - 1) * 0.5;
      const cz = (depth - 1) * 0.5;

      // Weathered stone plinth slabs across the footprint
      vox(cx, 0.07, cz, width * 0.94, 0.14, depth * 0.94, C.STN_D, g);
      vox(cx, 0.15, cz, width * 0.82, 0.04, depth * 0.82, C.STN_M, g);

      // Four corner / perimeter columns
      const p1X = cx - (width * 0.32), p1Z = cz - (depth * 0.32);
      vox(p1X, 0.32, p1Z, 0.32, 0.30, 0.32, C.STN_D, g);
      vox(p1X, 0.88, p1Z, 0.26, 0.82, 0.26, C.RUIN_ARCH, g);
      vox(p1X, 1.38, p1Z, 0.34, 0.20, 0.34, C.STN_L, g);
      vox(p1X, 1.49, p1Z, 0.20, 0.06, 0.20, C.MOSS, g);

      const p2X = cx + (width * 0.32), p2Z = cz - (depth * 0.32);
      vox(p2X, 0.32, p2Z, 0.32, 0.30, 0.32, C.STN_D, g);
      vox(p2X, 0.88, p2Z, 0.26, 0.82, 0.26, C.RUIN_ARCH, g);
      vox(p2X, 1.38, p2Z, 0.34, 0.20, 0.34, C.STN_L, g);

      const lintelLen = Math.hypot(p2X - p1X, p2Z - p1Z);
      vox(cx, 1.38, p1Z, lintelLen * 0.85, 0.16, 0.24, C.STN_M, g);
      vox(cx + 0.15, 1.18, p1Z + 0.08, 0.35, 0.16, 0.22, C.RUIN_ARCH, g);

      if (depth >= 2) {
        const p3X = cx - (width * 0.32), p3Z = cz + (depth * 0.32);
        vox(p3X, 0.30, p3Z, 0.32, 0.26, 0.32, C.STN_D, g);
        vox(p3X, 0.58, p3Z, 0.26, 0.32, 0.26, C.RUIN_ARCH, g);
        vox(p3X + 0.22, 0.14, p3Z - 0.12, 0.22, 0.16, 0.22, C.STN_L, g);

        const p4X = cx + (width * 0.32), p4Z = cz + (depth * 0.32);
        vox(p4X, 0.24, p4Z, 0.34, 0.20, 0.34, C.STN_D, g);
      }

      // Inlaid Glowing Runic Pattern in the stone floor
      const runeMeshes = [];
      const glyphCol = 0x39FF14;
      runeMeshes.push(vox(cx, 0.18, cz, 0.22, 0.04, 0.22, glyphCol, g, glyphCol, 2.0));
      runeMeshes.push(vox(cx, 0.18, cz - 0.25, 0.14, 0.04, 0.22, glyphCol, g, glyphCol, 1.7));
      runeMeshes.push(vox(cx, 0.18, cz + 0.25, 0.14, 0.04, 0.22, glyphCol, g, glyphCol, 1.7));
      runeMeshes.push(vox(cx - 0.25, 0.18, cz, 0.22, 0.04, 0.14, glyphCol, g, glyphCol, 1.7));
      runeMeshes.push(vox(cx + 0.25, 0.18, cz, 0.22, 0.04, 0.14, glyphCol, g, glyphCol, 1.7));
      g.userData.runeMeshes = runeMeshes;

      // Clay urns and spilled shards in corner
      vox(cx - (width * 0.25), 0.28, cz + (depth * 0.25), 0.20, 0.24, 0.20, C.TERRACOTTA, g);
      vox(cx - (width * 0.14), 0.20, cz + (depth * 0.32), 0.14, 0.12, 0.14, C.BG_BR, g);

      environmentalProps.push(g);

      if (parent) parent.add(g);
      return g;
    },

    // 11. Pottery Urns (Clay urns, amphora and shattered shards)
    spawnPotteryUrns: function (parent, x, y, z) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'pottery_urns';

      // Large Urn: base, belly, neck
      vox(-0.14, 0.11, -0.04, 0.24, 0.20, 0.24, C.TERRACOTTA, g);
      vox(-0.14, 0.29, -0.04, 0.32, 0.20, 0.32, C.BG_BR, g);
      vox(-0.14, 0.44, -0.04, 0.18, 0.12, 0.18, C.TERRA_RIM, g);
      // Tilted Medium Urn: base, belly, neck
      vox(0.18, 0.09, 0.08, 0.20, 0.16, 0.20, C.TERRACOTTA, g);
      vox(0.22, 0.22, 0.10, 0.24, 0.15, 0.24, C.BG_BR, g);
      vox(0.26, 0.33, 0.12, 0.15, 0.09, 0.15, C.TERRA_RIM, g);
      // Broken shards and spilled terracotta
      vox(0.07, 0.05, -0.20, 0.20, 0.09, 0.16, C.TERRACOTTA, g);
      vox(-0.30, 0.04, 0.14, 0.13, 0.06, 0.13, C.BG_BR, g);
      vox(0.26, 0.04, -0.04, 0.11, 0.05, 0.11, C.TERRA_RIM, g);

      if (parent) parent.add(g);
      return g;
    },

    // 12. Runic Glyph Tile (Ancient stone slab embedded with glowing green/gold runes)
    spawnRunicGlyphTile: function (parent, x, y, z) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'runic_glyph';

      const glyphCol = Math.random() < 0.65 ? C.GLOW_GRN : 0xFFD700;
      // Carved stone plinth
      vox(0, 0.06, 0, 0.86, 0.12, 0.86, C.STN_D, g);
      vox(0, 0.13, 0, 0.74, 0.04, 0.74, C.STN_M, g);

      // Inlaid glowing rune pattern
      const runeMeshes = [];
      runeMeshes.push(vox(0, 0.16, 0, 0.18, 0.04, 0.18, glyphCol, g, glyphCol, 2.0));
      runeMeshes.push(vox(0, 0.16, -0.22, 0.12, 0.04, 0.20, glyphCol, g, glyphCol, 1.8));
      runeMeshes.push(vox(0, 0.16,  0.22, 0.12, 0.04, 0.20, glyphCol, g, glyphCol, 1.8));
      runeMeshes.push(vox( 0.22, 0.16, 0, 0.20, 0.04, 0.12, glyphCol, g, glyphCol, 1.8));
      runeMeshes.push(vox(-0.22, 0.16, 0, 0.20, 0.04, 0.12, glyphCol, g, glyphCol, 1.8));
      runeMeshes.push(vox( 0.22, 0.16,  0.22, 0.08, 0.04, 0.08, glyphCol, g, glyphCol, 1.5));
      runeMeshes.push(vox(-0.22, 0.16, -0.22, 0.08, 0.04, 0.08, glyphCol, g, glyphCol, 1.5));

      g.userData.runeMeshes = runeMeshes;
      environmentalProps.push(g);

      if (parent) parent.add(g);
      return g;
    },

    // --------------------------------------------------------
    // SUPPLEMENTARY / COMPATIBILITY ASSETS
    // --------------------------------------------------------

    // Stout Golden Barrel Cactus
    spawnBarrelCactus: function (parent, x, y, z) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'barrel_cactus';
      vox(0, 0.22, 0, 0.45, 0.44, 0.45, C.CACT, g);
      vox(0, 0.22, 0, 0.52, 0.36, 0.3, C.CACT_D, g);
      vox(0, 0.22, 0, 0.3,  0.36, 0.52, C.CACT_D, g);
      vox(0, 0.46, 0, 0.22, 0.12, 0.22, C.FLOWER_Y, g, C.FLOWER_Y, 0.8);
      environmentalProps.push(g);
      if (parent) parent.add(g);
      return g;
    },

    // Desert Shrub / Sagebrush
    spawnDesertShrub: function (parent, x, y, z) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'desert_shrub';
      vox(0, 0.12, 0, 0.35, 0.24, 0.35, 0x556B2F, g);
      vox(0.1, 0.24, -0.05, 0.25, 0.2, 0.25, 0x6B8E23, g);
      vox(-0.08, 0.2, 0.08, 0.22, 0.18, 0.22, 0x8C7A58, g);
      environmentalProps.push(g);
      if (parent) parent.add(g);
      return g;
    },

    // Date Palm Tree (Gnarled curved trunk, coconuts, cascading fronds)
    spawnPalmTree: function (parent, x, y, z) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'palm_tree';

      // Segmented curved coconut trunk
      vox(0,    0.35, 0,    0.32, 0.70, 0.32, C.OG_WD_DK, g);
      vox(0.08, 1.00, 0.05, 0.28, 0.65, 0.28, C.OG_WD, g);
      vox(0.18, 1.65, 0.12, 0.26, 0.65, 0.26, C.OG_WD_DK, g);
      vox(0.28, 2.25, 0.20, 0.24, 0.60, 0.24, C.OG_WD, g);
      vox(0.36, 2.75, 0.28, 0.22, 0.45, 0.22, C.BED_1, g);

      // Crown group anchored at top of trunk so all fronds & coconuts sway together in the wind
      const crown = new THREE.Group();
      crown.position.set(0.36, 2.95, 0.28);
      crown.userData.baseY = 2.95;
      crown.userData.isCrown = true;

      // Coconuts clustered beneath fronds
      vox(-0.10, -0.10, -0.05, 0.16, 0.16, 0.16, 0x4A2E12, crown);
      vox( 0.12, -0.12,  0.08, 0.16, 0.16, 0.16, 0x4A2E12, crown);
      vox(-0.05, -0.12,  0.12, 0.16, 0.16, 0.16, 0x8B4513, crown);

      // Cascading multi-tiered palm fronds (Cross cardinal directions)
      vox( 0.45,  0.05,  0.00, 0.75, 0.08, 0.24, 0x228B22, crown);
      vox(-0.45,  0.05,  0.00, 0.75, 0.08, 0.24, 0x228B22, crown);
      vox( 0.00,  0.05,  0.45, 0.24, 0.08, 0.75, 0x228B22, crown);
      vox( 0.00,  0.05, -0.45, 0.24, 0.08, 0.75, 0x228B22, crown);

      // Diagonal arching fronds
      vox( 0.35,  0.10,  0.35, 0.55, 0.08, 0.55, 0x2E8B57, crown);
      vox(-0.35,  0.10, -0.35, 0.55, 0.08, 0.55, 0x2E8B57, crown);
      vox( 0.35,  0.10, -0.35, 0.55, 0.08, 0.55, 0x2E8B57, crown);
      vox(-0.35,  0.10,  0.35, 0.55, 0.08, 0.55, 0x2E8B57, crown);

      // Drooping tips
      vox( 0.80, -0.08,  0.00, 0.28, 0.15, 0.20, 0x1B7A43, crown);
      vox(-0.80, -0.08,  0.00, 0.28, 0.15, 0.20, 0x1B7A43, crown);
      vox( 0.00, -0.08,  0.80, 0.20, 0.15, 0.28, 0x1B7A43, crown);
      vox( 0.00, -0.08, -0.80, 0.20, 0.15, 0.28, 0x1B7A43, crown);

      g.add(crown);
      g.userData.crownGroup = crown;
      environmentalProps.push(g);

      if (parent) parent.add(g);
      return g;
    },

    // Cliffside Mini Waterfall (for elevation drops across sectors)
    spawnMiniWaterfall: function (parent, x, z, yTop, yBot) {
      const g = new THREE.Group();
      g.position.set(x, 0, z);
      g.userData.decorType = 'mini_waterfall';

      const h = yTop - yBot;
      // Flowing water column down cliff
      const fall = vox(0, yBot + h / 2, 0.5, 0.75, h, 0.18, C.WAT_M, g, C.WAT_M, 0.35, 0.90);
      fall.userData.baseY = fall.position.y;
      waterfallFlow.push(fall);

      // Frothing splash foam at foot of cliff
      const foam = vox(0, yBot + 0.08, 0.7, 0.85, 0.12, 0.28, C.WAT_FOAM, g, C.WAT_FOAM, 0.8);
      foam.userData.baseY = foam.position.y;
      waterfallFoam.push(foam);

      // Small splash pool
      const pool = vox(0, yBot + 0.04, 0.9, 0.95, 0.08, 0.65, C.WAT_M, g, C.WAT_M, 0.25, 0.88);
      pool.userData.baseY = pool.position.y;
      oasisWater.push(pool);

      if (parent) parent.add(g);
      return g;
    },

    // Sandstone Boulder / Rock Outcrop
    spawnSandstoneOutcrop: function (parent, x, y, z, scale = 1.0) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'sandstone_outcrop';
      vox(0, 0.3 * scale, 0, 0.9 * scale, 0.6 * scale, 0.85 * scale, C.SAND_X, g);
      vox(0.1 * scale, 0.6 * scale, -0.05 * scale, 0.7 * scale, 0.4 * scale, 0.65 * scale, C.SAND_D, g);
      vox(-0.1 * scale, 0.8 * scale, 0.05 * scale, 0.5 * scale, 0.3 * scale, 0.45 * scale, C.SAND_M, g);
      if (parent) parent.add(g);
      return g;
    },

    // Ancient Ruin Pillar
    spawnAncientRuinPillar: function (parent, x, y, z, h = 2) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'ruin_pillar';
      vox(0, 0.15, 0, 0.75, 0.3, 0.75, C.STN_D, g);
      for (let i = 0; i < h; i++) {
        vox(0, 0.45 + i * 0.5, 0, 0.52, 0.5, 0.52, (i % 2 === 0 ? C.STN_M : C.STN_L), g);
      }
      const topY = 0.45 + h * 0.5;
      vox(0, topY + 0.15, 0, 0.7, 0.3, 0.7, C.STN_D, g);
      vox(0, topY + 0.32, 0, 0.4, 0.1, 0.4, C.MOSS, g);
      if (parent) parent.add(g);
      return g;
    },

    // Runic Obelisk
    spawnRuneObelisk: function (parent, x, y, z) {
      const g = new THREE.Group();
      g.position.set(x, y, z);
      g.userData.decorType = 'rune_obelisk';
      vox(0, 0.2, 0, 0.7, 0.4, 0.7, C.STN_D, g);
      vox(0, 0.8, 0, 0.5, 0.8, 0.5, C.STN_M, g);
      vox(0, 1.5, 0, 0.35, 0.6, 0.35, C.STN_L, g);
      vox(0, 1.9, 0, 0.2, 0.3, 0.2, C.STN_M, g);
      vox(0, 0.9, 0.26, 0.12, 1.2, 0.05, C.GLOW_GRN, g, C.GLOW_GRN, 2.0);
      if (parent) parent.add(g);
      return g;
    }
  };

  // ========================================================
  // GOLEM CONFIGURATIONS
  // ========================================================
  const GOLEM_CONFIGS = {
    stone: {
      type: 'stone',
      name: 'First of Stone',
      title: 'Crag Hurler',
      cost: 50,
      damage: 28,
      range: 4.0,
      cooldown: 1.8,
      damageType: 'Physical',
      color: C.SG_M,
      desc: 'Launches heavy parabolic boulders with 1.8-tile AoE splash.',
      capstoneDesc: 'AoE explosion radius expands from 1.8 to 2.4 tiles.',
      ascendDesc: '👑 Mega Meteor: 3.2-tile AoE shockwave with devastating crater blast!'
    },
    oak: {
      type: 'oak',
      name: 'First of Oak',
      title: 'Bastion Cannon',
      cost: 40,
      damage: 18,
      range: 6.0,
      cooldown: 0.65,
      damageType: 'Physical',
      color: C.OG_TAN,
      desc: 'Rapid-fire sniper cannon firing high-velocity homing kinetic slugs.',
      capstoneDesc: 'Every 3rd cannon shot deals 2x Critical Kinetic Damage.',
      ascendDesc: '👑 Twin Ballista: 2x attack rate & every 2nd shot deals 2.5x Kinetic Crit!'
    },
    brick: {
      type: 'brick',
      name: 'First of Brick',
      title: 'Emerald Warden',
      cost: 65,
      damage: 22,
      range: 2.3,
      cooldown: 2.2,
      damageType: 'Physical',
      color: C.BG_BR,
      desc: 'Seismic ground slam: hits all enemies in range, applying Stun & Armor Shred.',
      capstoneDesc: 'Seismic Slam Stun duration increases to 1.0s.',
      ascendDesc: '👑 Cataclysmic Quake: 3.6-tile radius, 0.9s Stun & 40% Armor Shred!'
    },
    diorite: {
      type: 'diorite',
      name: 'First of Diorite',
      title: 'Solar Conduit',
      cost: 80,
      damage: 20,
      range: 4.5,
      cooldown: 1.1,
      damageType: 'Magic',
      color: C.DG_GLD,
      desc: 'Arcane solar beam: chains up to 3 enemies, pierces armor, applies 30% Slow.',
      capstoneDesc: 'Arcane beam chains to 3 secondary targets (4 total).',
      ascendDesc: '👑 Supernova Conduit: Chains 6 targets, deals heavy burn & 50% Slow for 3.5s!'
    }
  };

  // ========================================================
  // ALIEN ROSTER CONFIGURATIONS
  // ========================================================
  const ALIEN_CONFIGS = {
    scout: {
      type: 'scout',
      name: 'Alien Scout',
      baseHp: 45,
      speed: 2.4,
      shards: 8,
      penalty: 1,
      isBoss: false
    },
    trooper: {
      type: 'trooper',
      name: 'Void Trooper',
      baseHp: 95,
      speed: 1.4,
      shards: 14,
      penalty: 1,
      isBoss: false
    },
    shielder: {
      type: 'shielder',
      name: 'Phase Shielder',
      baseHp: 160,
      speed: 1.1,
      shards: 22,
      penalty: 2,
      isBoss: false
    },
    skitterer: {
      type: 'skitterer',
      name: 'Swarm Skitterer',
      baseHp: 35,
      speed: 3.0,
      shards: 5,
      penalty: 1,
      isBoss: false
    },
    boss: {
      type: 'boss',
      name: 'Astral Leviathan',
      baseHp: 2200,
      speed: 0.64,
      shards: 220,
      penalty: 5,
      isBoss: true
    }
  };

  // ========================================================
  // PROCEDURAL WEB AUDIO API SOUND SYNTHESIZER
  // ========================================================
  const SoundManager = {
    ctx: null,
    masterGain: null,
    sfxGain: null,
    ambientGain: null,
    windGain: null,
    waterGain: null,
    windSource: null,
    waterSource: null,
    ambientStarted: false,
    isMuted: false,
    masterVolume: 0.8,
    sfxVolume: 1.0,
    lastPlayTime: {},

    init: function () {
      if (this.ctx) return;
      try {
        const AudioCtx = window.AudioContext || window.webkitAudioContext;
        if (!AudioCtx) return;
        this.ctx = new AudioCtx();
        this.masterGain = this.ctx.createGain();
        this.masterGain.gain.value = this.isMuted ? 0 : this.masterVolume * 0.45;
        this.masterGain.connect(this.ctx.destination);

        this.sfxGain = this.ctx.createGain();
        this.sfxGain.gain.value = this.sfxVolume;
        this.sfxGain.connect(this.masterGain);
      } catch (e) {
        console.warn('Web Audio API not supported:', e);
      }
    },

    initAmbience: function () {
      if (!this.ctx || this.ambientGain) return;
      try {
        this.ambientGain = this.ctx.createGain();
        this.ambientGain.gain.setValueAtTime(this.isMuted ? 0 : 0.8, this.ctx.currentTime);
        this.ambientGain.connect(this.masterGain);

        // 1. Desert Wind Synthesizer (3s continuous pink/brown noise loop)
        const sampleRate = this.ctx.sampleRate;
        const windBuf = this.ctx.createBuffer(1, sampleRate * 3, sampleRate);
        const windData = windBuf.getChannelData(0);
        let b0 = 0, b1 = 0, b2 = 0;
        for (let i = 0; i < windData.length; i++) {
          const white = Math.random() * 2 - 1;
          b0 = 0.99886 * b0 + white * 0.0555179;
          b1 = 0.99332 * b1 + white * 0.0750759;
          b2 = 0.96900 * b2 + white * 0.1538520;
          windData[i] = (b0 + b1 + b2) * 0.11;
        }

        this.windSource = this.ctx.createBufferSource();
        this.windSource.buffer = windBuf;
        this.windSource.loop = true;

        const windFilter = this.ctx.createBiquadFilter();
        windFilter.type = 'lowpass';
        windFilter.frequency.setValueAtTime(340, this.ctx.currentTime);
        windFilter.Q.setValueAtTime(1.8, this.ctx.currentTime);

        // Gentle LFO sweeping wind filter cutoff (natural breathing wind)
        const windLfo = this.ctx.createOscillator();
        const windLfoGain = this.ctx.createGain();
        windLfo.frequency.setValueAtTime(0.18, this.ctx.currentTime);
        windLfoGain.gain.setValueAtTime(140, this.ctx.currentTime);
        windLfo.connect(windLfoGain);
        windLfoGain.connect(windFilter.frequency);
        windLfo.start();

        this.windGain = this.ctx.createGain();
        this.windGain.gain.setValueAtTime(0.08, this.ctx.currentTime);

        this.windSource.connect(windFilter);
        windFilter.connect(this.windGain);
        this.windGain.connect(this.ambientGain);
        this.windSource.start();

        // 2. Water Trickle / Waterfall Murmur Synthesizer (2s filtered noise loop)
        const waterBuf = this.ctx.createBuffer(1, sampleRate * 2, sampleRate);
        const waterData = waterBuf.getChannelData(0);
        for (let i = 0; i < waterData.length; i++) {
          waterData[i] = (Math.random() * 2 - 1) * 0.08;
        }

        this.waterSource = this.ctx.createBufferSource();
        this.waterSource.buffer = waterBuf;
        this.waterSource.loop = true;

        const waterFilter = this.ctx.createBiquadFilter();
        waterFilter.type = 'bandpass';
        waterFilter.frequency.setValueAtTime(1100, this.ctx.currentTime);
        waterFilter.Q.setValueAtTime(3.2, this.ctx.currentTime);

        // Gentle LFO for bubbling brook / cascade shimmer
        const waterLfo = this.ctx.createOscillator();
        const waterLfoGain = this.ctx.createGain();
        waterLfo.frequency.setValueAtTime(0.75, this.ctx.currentTime);
        waterLfoGain.gain.setValueAtTime(320, this.ctx.currentTime);
        waterLfo.connect(waterLfoGain);
        waterLfoGain.connect(waterFilter.frequency);
        waterLfo.start();

        this.waterGain = this.ctx.createGain();
        this.waterGain.gain.setValueAtTime(0.05, this.ctx.currentTime);

        this.waterSource.connect(waterFilter);
        waterFilter.connect(this.waterGain);
        this.waterGain.connect(this.ambientGain);
        this.waterSource.start();

        this.ambientStarted = true;
      } catch (err) {
        console.warn('Ambient sound init error:', err);
      }
    },

    startAmbience: function () {
      this.resumeContext();
      if (!this.ambientStarted) {
        this.initAmbience();
      }
    },

    updateAmbience: function (windGust) {
      if (!this.windGain || this.isMuted) return;
      const targetGain = 0.06 + ((windGust || 1.0) - 1.0) * 0.04;
      this.windGain.gain.setTargetAtTime(Math.max(0.03, Math.min(0.14, targetGain)), this.ctx.currentTime, 0.2);
    },

    setMasterVolume: function (val) {
      this.masterVolume = Math.max(0, Math.min(1, val));
      if (this.masterGain && !this.isMuted) {
        this.masterGain.gain.value = this.masterVolume * 0.45;
      }
      const label = document.getElementById('label-master-vol');
      if (label) label.textContent = `${Math.round(this.masterVolume * 100)}%`;
    },

    setSfxVolume: function (val) {
      this.sfxVolume = Math.max(0, Math.min(1, val));
      if (this.sfxGain) {
        this.sfxGain.gain.value = this.sfxVolume;
      }
      const label = document.getElementById('label-sfx-vol');
      if (label) label.textContent = `${Math.round(this.sfxVolume * 100)}%`;
    },

    resumeContext: function () {
      if (!this.ctx) this.init();
      if (this.ctx && this.ctx.state === 'suspended') {
        this.ctx.resume();
      }
      if (!this.ambientStarted && this.ctx) {
        this.initAmbience();
      }
    },

    toggleMute: function () {
      this.isMuted = !this.isMuted;
      if (this.masterGain) {
        this.masterGain.gain.value = this.isMuted ? 0 : this.masterVolume * 0.45;
      }
      if (this.ambientGain) {
        this.ambientGain.gain.value = this.isMuted ? 0 : 0.8;
      }
      const btn = document.getElementById('btn-audio');
      if (btn) {
        btn.textContent = this.isMuted ? '🔇 SFX: MUTE' : '🔊 SFX: ON';
        btn.classList.toggle('muted', this.isMuted);
      }
      const btnSettings = document.getElementById('btn-toggle-mute-settings');
      if (btnSettings) {
        btnSettings.textContent = this.isMuted ? '🔇 AUDIO: MUTED' : '🔊 AUDIO: ON';
      }
      return this.isMuted;
    },

    play: function (soundName) {
      if (this.isMuted) return;
      this.resumeContext();
      if (!this.ctx) return;

      const now = performance.now();
      // Polyphony throttling: minimum 40ms between identical SFX calls
      if (this.lastPlayTime[soundName] && (now - this.lastPlayTime[soundName] < 40)) {
        return;
      }
      this.lastPlayTime[soundName] = now;

      const t = this.ctx.currentTime;
      const targetGain = this.sfxGain || this.masterGain;

      switch (soundName) {
        case 'summon':
        case 'golemPlace': {
          // Low-frequency sawtooth + filtered noise sweep (120Hz -> 60Hz, 0.25s) stone grinding
          const osc = this.ctx.createOscillator();
          const gain = this.ctx.createGain();
          osc.type = 'sawtooth';
          osc.frequency.setValueAtTime(120, t);
          osc.frequency.exponentialRampToValueAtTime(60, t + 0.25);
          gain.gain.setValueAtTime(0.5, t);
          gain.gain.exponentialRampToValueAtTime(0.01, t + 0.25);
          osc.connect(gain);
          gain.connect(targetGain);
          osc.start(t);
          osc.stop(t + 0.25);
          break;
        }

        case 'upgrade': {
          // Crystalline chime (523Hz -> 784Hz)
          [523.25, 659.25, 783.99].forEach((freq, idx) => {
            const osc = this.ctx.createOscillator();
            const gain = this.ctx.createGain();
            osc.type = 'triangle';
            osc.frequency.setValueAtTime(freq, t + idx * 0.05);
            gain.gain.setValueAtTime(0.4, t + idx * 0.05);
            gain.gain.exponentialRampToValueAtTime(0.01, t + idx * 0.05 + 0.25);
            osc.connect(gain);
            gain.connect(targetGain);
            osc.start(t + idx * 0.05);
            osc.stop(t + idx * 0.05 + 0.25);
          });
          break;
        }

        case 'ascension': {
          // Grand celestial arpeggio (C5, E5, G5, B5, C6, E6)
          [523.25, 659.25, 783.99, 987.77, 1046.50, 1318.51].forEach((freq, idx) => {
            const osc = this.ctx.createOscillator();
            const gain = this.ctx.createGain();
            osc.type = 'sine';
            osc.frequency.setValueAtTime(freq, t + idx * 0.06);
            gain.gain.setValueAtTime(0.35, t + idx * 0.06);
            gain.gain.exponentialRampToValueAtTime(0.001, t + idx * 0.06 + 0.5);
            osc.connect(gain);
            gain.connect(targetGain);
            osc.start(t + idx * 0.06);
            osc.stop(t + idx * 0.06 + 0.5);
          });
          break;
        }

        case 'stoneRumble': {
          // Deep earth-shaking rumble (80Hz down to 25Hz, 1.2s duration)
          const osc = this.ctx.createOscillator();
          const gain = this.ctx.createGain();
          osc.type = 'sawtooth';
          osc.frequency.setValueAtTime(80, t);
          osc.frequency.exponentialRampToValueAtTime(25, t + 1.2);
          gain.gain.setValueAtTime(0.5, t);
          gain.gain.exponentialRampToValueAtTime(0.01, t + 1.2);
          osc.connect(gain);
          gain.connect(targetGain);
          osc.start(t);
          osc.stop(t + 1.2);
          break;
        }

        case 'expansionUnlock': {
          // Ancient fanfaric chord (D4, A4, D5, F#5)
          [293.66, 440.00, 587.33, 739.99].forEach(freq => {
            const osc = this.ctx.createOscillator();
            const gain = this.ctx.createGain();
            osc.type = 'triangle';
            osc.frequency.setValueAtTime(freq, t);
            gain.gain.setValueAtTime(0.3, t);
            gain.gain.exponentialRampToValueAtTime(0.005, t + 0.8);
            osc.connect(gain);
            gain.connect(targetGain);
            osc.start(t);
            osc.stop(t + 0.8);
          });
          break;
        }

        case 'stoneThrow':
        case 'stoneImpact': {
          // Deep triangle sub-thud (90Hz -> 30Hz, 0.22s) + low-pass noise burst
          const osc = this.ctx.createOscillator();
          const gain = this.ctx.createGain();
          osc.type = 'triangle';
          osc.frequency.setValueAtTime(90, t);
          osc.frequency.exponentialRampToValueAtTime(30, t + 0.22);
          gain.gain.setValueAtTime(0.6, t);
          gain.gain.exponentialRampToValueAtTime(0.01, t + 0.22);
          osc.connect(gain);
          gain.connect(this.masterGain);
          osc.start(t);
          osc.stop(t + 0.22);
          break;
        }

        case 'oakShoot': {
          // Punchy square-wave pitch drop (320Hz -> 110Hz, 0.08s)
          const osc = this.ctx.createOscillator();
          const gain = this.ctx.createGain();
          osc.type = 'square';
          osc.frequency.setValueAtTime(320, t);
          osc.frequency.exponentialRampToValueAtTime(110, t + 0.08);
          gain.gain.setValueAtTime(0.35, t);
          gain.gain.exponentialRampToValueAtTime(0.01, t + 0.08);
          osc.connect(gain);
          gain.connect(this.masterGain);
          osc.start(t);
          osc.stop(t + 0.08);
          break;
        }

        case 'brickSlam': {
          // Heavy bass pulse (65Hz -> 28Hz, 0.35s) + metallic ring (440Hz sine decay)
          const bass = this.ctx.createOscillator();
          const bassGain = this.ctx.createGain();
          bass.type = 'sawtooth';
          bass.frequency.setValueAtTime(65, t);
          bass.frequency.exponentialRampToValueAtTime(28, t + 0.35);
          bassGain.gain.setValueAtTime(0.7, t);
          bassGain.gain.exponentialRampToValueAtTime(0.01, t + 0.35);
          bass.connect(bassGain);
          bassGain.connect(this.masterGain);
          bass.start(t);
          bass.stop(t + 0.35);

          const ring = this.ctx.createOscillator();
          const ringGain = this.ctx.createGain();
          ring.type = 'sine';
          ring.frequency.setValueAtTime(440, t);
          ring.frequency.exponentialRampToValueAtTime(220, t + 0.25);
          ringGain.gain.setValueAtTime(0.3, t);
          ringGain.gain.exponentialRampToValueAtTime(0.01, t + 0.25);
          ring.connect(ringGain);
          ringGain.connect(this.masterGain);
          ring.start(t);
          ring.stop(t + 0.25);
          break;
        }

        case 'dioriteBeam': {
          // Dual detuned sine/triangle oscillators (660Hz & 668Hz -> 880Hz, 0.15s)
          [660, 668].forEach(freq => {
            const osc = this.ctx.createOscillator();
            const gain = this.ctx.createGain();
            osc.type = 'sine';
            osc.frequency.setValueAtTime(freq, t);
            osc.frequency.linearRampToValueAtTime(880, t + 0.15);
            gain.gain.setValueAtTime(0.3, t);
            gain.gain.exponentialRampToValueAtTime(0.01, t + 0.15);
            osc.connect(gain);
            gain.connect(this.masterGain);
            osc.start(t);
            osc.stop(t + 0.15);
          });
          break;
        }

        case 'enemyHit': {
          const osc = this.ctx.createOscillator();
          const gain = this.ctx.createGain();
          osc.type = 'triangle';
          osc.frequency.setValueAtTime(200, t);
          osc.frequency.exponentialRampToValueAtTime(80, t + 0.05);
          gain.gain.setValueAtTime(0.2, t);
          gain.gain.exponentialRampToValueAtTime(0.01, t + 0.05);
          osc.connect(gain);
          gain.connect(this.masterGain);
          osc.start(t);
          osc.stop(t + 0.05);
          break;
        }

        case 'enemyDeath': {
          // Crisp high-pitched pop (400Hz -> 900Hz, 0.1s)
          const osc = this.ctx.createOscillator();
          const gain = this.ctx.createGain();
          osc.type = 'square';
          osc.frequency.setValueAtTime(400, t);
          osc.frequency.exponentialRampToValueAtTime(900, t + 0.1);
          gain.gain.setValueAtTime(0.3, t);
          gain.gain.exponentialRampToValueAtTime(0.01, t + 0.1);
          osc.connect(gain);
          gain.connect(this.masterGain);
          osc.start(t);
          osc.stop(t + 0.1);
          break;
        }

        case 'waveStart': {
          // Deep resonant brass-like horn chord
          [146.83, 220.00, 293.66].forEach(freq => {
            const osc = this.ctx.createOscillator();
            const gain = this.ctx.createGain();
            osc.type = 'sawtooth';
            osc.frequency.setValueAtTime(freq, t);
            gain.gain.setValueAtTime(0.25, t);
            gain.gain.exponentialRampToValueAtTime(0.01, t + 0.6);
            osc.connect(gain);
            gain.connect(this.masterGain);
            osc.start(t);
            osc.stop(t + 0.6);
          });
          break;
        }

        case 'sanctumDamage': {
          // Low dissonant alarm buzz (150Hz + 110Hz sawtooth)
          [150, 110].forEach(freq => {
            const osc = this.ctx.createOscillator();
            const gain = this.ctx.createGain();
            osc.type = 'sawtooth';
            osc.frequency.setValueAtTime(freq, t);
            gain.gain.setValueAtTime(0.4, t);
            gain.gain.exponentialRampToValueAtTime(0.01, t + 0.35);
            osc.connect(gain);
            gain.connect(this.masterGain);
            osc.start(t);
            osc.stop(t + 0.35);
          });
          break;
        }

        case 'sell': {
          [659.25, 523.25].forEach((freq, idx) => {
            const osc = this.ctx.createOscillator();
            const gain = this.ctx.createGain();
            osc.type = 'triangle';
            osc.frequency.setValueAtTime(freq, t + idx * 0.08);
            gain.gain.setValueAtTime(0.3, t + idx * 0.08);
            gain.gain.exponentialRampToValueAtTime(0.01, t + idx * 0.08 + 0.2);
            osc.connect(gain);
            gain.connect(this.masterGain);
            osc.start(t + idx * 0.08);
            osc.stop(t + idx * 0.08 + 0.2);
          });
          break;
        }

        case 'error': {
          const osc = this.ctx.createOscillator();
          const gain = this.ctx.createGain();
          osc.type = 'square';
          osc.frequency.setValueAtTime(110, t);
          gain.gain.setValueAtTime(0.3, t);
          gain.gain.exponentialRampToValueAtTime(0.01, t + 0.1);
          osc.connect(gain);
          gain.connect(this.masterGain);
          osc.start(t);
          osc.stop(t + 0.1);
          break;
        }

        case 'bossAura': {
          const osc = this.ctx.createOscillator();
          const gain = this.ctx.createGain();
          osc.type = 'triangle';
          osc.frequency.setValueAtTime(55, t);
          osc.frequency.linearRampToValueAtTime(80, t + 0.4);
          gain.gain.setValueAtTime(0.5, t);
          gain.gain.exponentialRampToValueAtTime(0.01, t + 0.4);
          osc.connect(gain);
          gain.connect(this.masterGain);
          osc.start(t);
          osc.stop(t + 0.4);
          break;
        }

        case 'victory': {
          [523.25, 659.25, 783.99, 1046.50].forEach((freq, idx) => {
            const osc = this.ctx.createOscillator();
            const gain = this.ctx.createGain();
            osc.type = 'triangle';
            osc.frequency.setValueAtTime(freq, t + idx * 0.12);
            gain.gain.setValueAtTime(0.4, t + idx * 0.12);
            gain.gain.exponentialRampToValueAtTime(0.01, t + idx * 0.12 + 0.4);
            osc.connect(gain);
            gain.connect(this.masterGain);
            osc.start(t + idx * 0.12);
            osc.stop(t + idx * 0.12 + 0.4);
          });
          break;
        }

        case 'defeat': {
          [220, 196, 174.61, 130.81].forEach((freq, idx) => {
            const osc = this.ctx.createOscillator();
            const gain = this.ctx.createGain();
            osc.type = 'sawtooth';
            osc.frequency.setValueAtTime(freq, t + idx * 0.15);
            gain.gain.setValueAtTime(0.35, t + idx * 0.15);
            gain.gain.exponentialRampToValueAtTime(0.01, t + idx * 0.15 + 0.35);
            osc.connect(gain);
            gain.connect(this.masterGain);
            osc.start(t + idx * 0.15);
            osc.stop(t + idx * 0.15 + 0.35);
          });
          break;
        }

        case 'portalCollapse': {
          const osc = this.ctx.createOscillator();
          const gain = this.ctx.createGain();
          osc.type = 'sawtooth';
          osc.frequency.setValueAtTime(280, t);
          osc.frequency.exponentialRampToValueAtTime(40, t + 0.65);
          gain.gain.setValueAtTime(0.45, t);
          gain.gain.exponentialRampToValueAtTime(0.001, t + 0.7);
          osc.connect(gain);
          gain.connect(this.masterGain);
          osc.start(t);
          osc.stop(t + 0.7);
          break;
        }

        // --- Elemental Attacks & Status SFX ---
        case 'thunderAttack': {
          const osc = this.ctx.createOscillator();
          const gain = this.ctx.createGain();
          osc.type = 'sawtooth';
          osc.frequency.setValueAtTime(880, t);
          osc.frequency.exponentialRampToValueAtTime(140, t + 0.18);
          gain.gain.setValueAtTime(0.4, t);
          gain.gain.exponentialRampToValueAtTime(0.01, t + 0.2);
          osc.connect(gain);
          gain.connect(this.masterGain);
          osc.start(t);
          osc.stop(t + 0.2);
          break;
        }

        case 'earthAttack': {
          const osc = this.ctx.createOscillator();
          const gain = this.ctx.createGain();
          osc.type = 'triangle';
          osc.frequency.setValueAtTime(90, t);
          osc.frequency.exponentialRampToValueAtTime(30, t + 0.28);
          gain.gain.setValueAtTime(0.6, t);
          gain.gain.exponentialRampToValueAtTime(0.01, t + 0.3);
          osc.connect(gain);
          gain.connect(this.masterGain);
          osc.start(t);
          osc.stop(t + 0.3);
          break;
        }

        case 'fireAttack': {
          const osc = this.ctx.createOscillator();
          const gain = this.ctx.createGain();
          osc.type = 'sawtooth';
          osc.frequency.setValueAtTime(440, t);
          osc.frequency.exponentialRampToValueAtTime(80, t + 0.25);
          gain.gain.setValueAtTime(0.38, t);
          gain.gain.exponentialRampToValueAtTime(0.01, t + 0.28);
          osc.connect(gain);
          gain.connect(this.masterGain);
          osc.start(t);
          osc.stop(t + 0.28);
          break;
        }

        case 'waterAttack': {
          const osc = this.ctx.createOscillator();
          const gain = this.ctx.createGain();
          osc.type = 'sine';
          osc.frequency.setValueAtTime(320, t);
          osc.frequency.linearRampToValueAtTime(540, t + 0.1);
          osc.frequency.exponentialRampToValueAtTime(180, t + 0.24);
          gain.gain.setValueAtTime(0.42, t);
          gain.gain.exponentialRampToValueAtTime(0.01, t + 0.26);
          osc.connect(gain);
          gain.connect(this.masterGain);
          osc.start(t);
          osc.stop(t + 0.26);
          break;
        }

        case 'electrocuteTick': {
          const osc = this.ctx.createOscillator();
          const gain = this.ctx.createGain();
          osc.type = 'square';
          osc.frequency.setValueAtTime(1100, t);
          osc.frequency.setValueAtTime(750, t + 0.04);
          gain.gain.setValueAtTime(0.25, t);
          gain.gain.exponentialRampToValueAtTime(0.01, t + 0.09);
          osc.connect(gain);
          gain.connect(this.masterGain);
          osc.start(t);
          osc.stop(t + 0.09);
          break;
        }

        case 'burnTick': {
          const osc = this.ctx.createOscillator();
          const gain = this.ctx.createGain();
          osc.type = 'sawtooth';
          osc.frequency.setValueAtTime(260, t);
          osc.frequency.exponentialRampToValueAtTime(90, t + 0.12);
          gain.gain.setValueAtTime(0.22, t);
          gain.gain.exponentialRampToValueAtTime(0.01, t + 0.13);
          osc.connect(gain);
          gain.connect(this.masterGain);
          osc.start(t);
          osc.stop(t + 0.13);
          break;
        }

        case 'knockbackImpact': {
          const osc = this.ctx.createOscillator();
          const gain = this.ctx.createGain();
          osc.type = 'sine';
          osc.frequency.setValueAtTime(110, t);
          osc.frequency.exponentialRampToValueAtTime(35, t + 0.18);
          gain.gain.setValueAtTime(0.5, t);
          gain.gain.exponentialRampToValueAtTime(0.01, t + 0.2);
          osc.connect(gain);
          gain.connect(this.masterGain);
          osc.start(t);
          osc.stop(t + 0.2);
          break;
        }

        case 'combustionExplode': {
          const osc = this.ctx.createOscillator();
          const gain = this.ctx.createGain();
          osc.type = 'sawtooth';
          osc.frequency.setValueAtTime(180, t);
          osc.frequency.exponentialRampToValueAtTime(25, t + 0.45);
          gain.gain.setValueAtTime(0.65, t);
          gain.gain.exponentialRampToValueAtTime(0.01, t + 0.5);
          osc.connect(gain);
          gain.connect(this.masterGain);
          osc.start(t);
          osc.stop(t + 0.5);
          break;
        }

        case 'tornadoRoar': {
          [160, 240, 360].forEach((freq, idx) => {
            const osc = this.ctx.createOscillator();
            const gain = this.ctx.createGain();
            osc.type = 'sawtooth';
            osc.frequency.setValueAtTime(freq, t);
            osc.frequency.linearRampToValueAtTime(freq * 1.5, t + 0.7);
            osc.frequency.linearRampToValueAtTime(freq * 0.8, t + 1.5);
            gain.gain.setValueAtTime(0.18, t);
            gain.gain.exponentialRampToValueAtTime(0.01, t + 1.5);
            osc.connect(gain);
            gain.connect(this.masterGain);
            osc.start(t);
            osc.stop(t + 1.5);
          });
          break;
        }

        case 'uniqueSpawn': {
          [523.25, 659.25, 783.99, 1046.50].forEach((freq, idx) => {
            const osc = this.ctx.createOscillator();
            const gain = this.ctx.createGain();
            osc.type = 'sine';
            osc.frequency.setValueAtTime(freq, t + idx * 0.08);
            gain.gain.setValueAtTime(0.3, t + idx * 0.08);
            gain.gain.exponentialRampToValueAtTime(0.01, t + idx * 0.08 + 0.35);
            osc.connect(gain);
            gain.connect(this.masterGain);
            osc.start(t + idx * 0.08);
            osc.stop(t + idx * 0.08 + 0.35);
          });
          break;
        }

        case 'auraPulse': {
          const osc = this.ctx.createOscillator();
          const gain = this.ctx.createGain();
          osc.type = 'sine';
          osc.frequency.setValueAtTime(392, t);
          osc.frequency.exponentialRampToValueAtTime(523.25, t + 0.25);
          gain.gain.setValueAtTime(0.2, t);
          gain.gain.exponentialRampToValueAtTime(0.01, t + 0.3);
          osc.connect(gain);
          gain.connect(this.masterGain);
          osc.start(t);
          osc.stop(t + 0.3);
          break;
        }

        case 'essenceGain': {
          [880, 1174.66, 1760].forEach((freq, idx) => {
            const osc = this.ctx.createOscillator();
            const gain = this.ctx.createGain();
            osc.type = 'sine';
            osc.frequency.setValueAtTime(freq, t + idx * 0.1);
            gain.gain.setValueAtTime(0.35, t + idx * 0.1);
            gain.gain.exponentialRampToValueAtTime(0.005, t + idx * 0.1 + 0.4);
            osc.connect(gain);
            gain.connect(this.masterGain);
            osc.start(t + idx * 0.1);
            osc.stop(t + idx * 0.1 + 0.4);
          });
          break;
        }

        case 'elementInfuse': {
          [330, 440, 554.37, 659.25].forEach((freq, idx) => {
            const osc = this.ctx.createOscillator();
            const gain = this.ctx.createGain();
            osc.type = 'triangle';
            osc.frequency.setValueAtTime(freq, t + idx * 0.09);
            gain.gain.setValueAtTime(0.38, t + idx * 0.09);
            gain.gain.exponentialRampToValueAtTime(0.01, t + idx * 0.09 + 0.35);
            osc.connect(gain);
            gain.connect(this.masterGain);
            osc.start(t + idx * 0.09);
            osc.stop(t + idx * 0.09 + 0.35);
          });
          break;
        }
      }
    }
  };

  // Expose SoundManager for external/test triggers
  window.SoundManager = SoundManager;

  // ========================================================
  // PROCEDURAL WIND SYSTEM & DIEGETIC SURFACE STREAMLINES
  // ========================================================
  const WindManager = {
    dir: new THREE.Vector3(0.85, 0, 0.52).normalize(),
    time: 0,
    gust: 1.0,
    particles: [],
    group: null,

    init: function (parent) {
      if (this.group && this.group.parent) {
        this.group.parent.remove(this.group);
      }
      this.group = new THREE.Group();
      this.particles = [];

      // Streamlined wind ribbons flowing smoothly over the overworld surface
      const count = 18;
      const angle = Math.atan2(this.dir.x, this.dir.z) - Math.PI / 2;

      for (let i = 0; i < count; i++) {
        const lineGroup = new THREE.Group();
        const length = 1.4 + Math.random() * 0.9;
        const width = 0.05 + Math.random() * 0.03;

        // Core wind streak
        const mat = new THREE.MeshBasicMaterial({
          color: Math.random() < 0.7 ? 0xFFFBE0 : 0xF7EBC6,
          transparent: true,
          opacity: 0.0,
          depthWrite: false
        });
        const mainMesh = new THREE.Mesh(getGeo(length, 0.02, width), mat);
        mainMesh.rotation.y = angle;
        lineGroup.add(mainMesh);

        // Leading wispy tip
        const tipMat = mat.clone();
        const tipMesh = new THREE.Mesh(getGeo(length * 0.45, 0.015, width * 0.6), tipMat);
        tipMesh.position.set(this.dir.x * (length * 0.38), 0, this.dir.z * (length * 0.38));
        tipMesh.rotation.y = angle;
        lineGroup.add(tipMesh);

        lineGroup.userData.mainMat = mat;
        lineGroup.userData.tipMat = tipMat;
        lineGroup.userData.speed = 2.2 + Math.random() * 1.6;
        lineGroup.userData.elevationOffset = 0.12 + Math.random() * 0.12;
        lineGroup.userData.maxOpacity = 0.28 + Math.random() * 0.16;
        lineGroup.userData.duration = 2.4 + Math.random() * 2.2;
        // Stagger initial progress so wind lines fade in and out continuously
        lineGroup.userData.life = Math.random() * lineGroup.userData.duration;

        this.resetWindLine(lineGroup, true);
        this.particles.push(lineGroup);
        this.group.add(lineGroup);
      }

      if (parent) parent.add(this.group);
    },

    isOverTerrain: function (x, z) {
      if (typeof ChunkManager !== 'undefined' && ChunkManager.chunks && ChunkManager.chunks.size > 0) {
        for (const [key, chunk] of ChunkManager.chunks.entries()) {
          const minX = chunk.cx * 16;
          const maxX = minX + 16;
          const minZ = chunk.cz * 16;
          const maxZ = minZ + 16;
          if (x >= minX + 0.4 && x <= maxX - 0.4 && z >= minZ + 0.4 && z <= maxZ - 0.4) {
            return true;
          }
        }
        return false;
      }
      return (x >= 0.4 && x <= 15.6 && z >= 0.4 && z <= 15.6);
    },

    getRandomTerrainPos: function () {
      let activeChunks = [{ cx: 0, cz: 0 }];
      if (typeof ChunkManager !== 'undefined' && ChunkManager.chunks && ChunkManager.chunks.size > 0) {
        activeChunks = Array.from(ChunkManager.chunks.values());
      }
      const chk = activeChunks[Math.floor(Math.random() * activeChunks.length)];
      const minX = chk.cx * 16 + 1.0;
      const maxX = chk.cx * 16 + 15.0;
      const minZ = chk.cz * 16 + 1.0;
      const maxZ = chk.cz * 16 + 15.0;

      const rx = minX + Math.random() * (maxX - minX);
      const rz = minZ + Math.random() * (maxZ - minZ);
      return { x: rx, z: rz };
    },

    resetWindLine: function (p, initial = false) {
      const pos = this.getRandomTerrainPos();
      p.position.x = pos.x;
      p.position.z = pos.z;
      const groundY = getTerrainHeight(pos.x, pos.z);
      p.position.y = groundY + p.userData.elevationOffset;

      p.userData.duration = 2.4 + Math.random() * 2.2;
      p.userData.speed = 2.0 + Math.random() * 1.6;
      p.userData.maxOpacity = 0.28 + Math.random() * 0.16;
      p.userData.life = initial ? Math.random() * p.userData.duration : 0;

      const prog = Math.min(1.0, p.userData.life / p.userData.duration);
      const op = p.userData.maxOpacity * Math.sin(prog * Math.PI);
      p.userData.mainMat.opacity = op;
      p.userData.tipMat.opacity = op * 0.75;
    },

    update: function (dt, t) {
      this.time = t;
      this.gust = 1.0 + Math.sin(t * 0.45) * 0.45 + Math.sin(t * 1.25) * 0.25;
      const moveStep = dt * this.gust;

      for (let i = 0; i < this.particles.length; i++) {
        const p = this.particles[i];
        p.userData.life += dt;

        // Smooth sinusoidal ease-in and ease-out
        if (p.userData.life >= p.userData.duration) {
          this.resetWindLine(p, false);
          continue;
        }

        const prog = Math.min(1.0, p.userData.life / p.userData.duration);
        const curOpacity = p.userData.maxOpacity * Math.sin(prog * Math.PI);
        p.userData.mainMat.opacity = curOpacity;
        p.userData.tipMat.opacity = curOpacity * 0.75;

        // Move along wind directional vector
        p.position.x += this.dir.x * moveStep * p.userData.speed;
        p.position.z += this.dir.z * moveStep * p.userData.speed;

        // Smoothly contour terrain elevation
        const groundY = getTerrainHeight(p.position.x, p.position.z);
        const targetY = groundY + p.userData.elevationOffset;
        p.position.y += (targetY - p.position.y) * 0.20;

        // Respawn if leaving active overworld bounds
        if (!this.isOverTerrain(p.position.x, p.position.z)) {
          this.resetWindLine(p, false);
        }
      }
    }
  };

  // ========================================================
  // 2D FLOATING WORLD-TO-SCREEN TEXT MANAGER
  // ========================================================
  const FloatingTextManager = {
    container: null,
    activeTexts: [],

    init: function () {
      this.container = document.getElementById('floating-text-container');
    },

    spawnText: function (worldPos, text, className = '') {
      if (!this.container) this.init();
      if (!this.container) return;

      const el = document.createElement('div');
      el.className = `floating-text ${className}`;
      el.textContent = text;
      this.container.appendChild(el);

      this.activeTexts.push({
        element: el,
        worldPos: worldPos.clone(),
        yOffset: 0.8,
        life: 0.8,
        maxLife: 0.8
      });
    },

    update: function (dt) {
      if (!camera) return;
      for (let i = this.activeTexts.length - 1; i >= 0; i--) {
        const item = this.activeTexts[i];
        item.life -= dt;
        item.yOffset += 1.2 * dt; // Float upward

        if (item.life <= 0) {
          if (item.element.parentNode) item.element.parentNode.removeChild(item.element);
          this.activeTexts.splice(i, 1);
          continue;
        }

        // Project 3D world position to 2D screen coordinates
        const projPos = item.worldPos.clone();
        projPos.y += item.yOffset;
        projPos.project(camera);

        const x = (projPos.x * 0.5 + 0.5) * window.innerWidth;
        const y = (-(projPos.y * 0.5) + 0.5) * window.innerHeight;

        item.element.style.transform = `translate(-50%, -50%) translate(${x}px, ${y}px)`;
        item.element.style.opacity = Math.max(0, item.life / item.maxLife).toFixed(2);
      }
    },

    clear: function () {
      this.activeTexts.forEach(t => {
        if (t.element.parentNode) t.element.parentNode.removeChild(t.element);
      });
      this.activeTexts = [];
    }
  };

  window.FloatingTextManager = FloatingTextManager;

  // ========================================================
  // STATE MANAGEMENT (Phase 3 Complete)
  // ========================================================
  const GameState = {
    shards: 150,
    essence: 0, // Astral Essence currency (Dropped exclusively by Bosses)
    sanctumHp: 20,
    maxSanctumHp: 20,
    currentWave: 0,
    totalWaves: 10,
    waveActive: false,
    gameSpeed: 1.0,
    selectedGolemType: 'stone',
    selectedPedestal: null,
    selectedGolem: null,
    gameOver: false,
    gameWon: false,
    endlessMode: false,
    inTitleScreen: true,
    vignetteEnabled: true,
    realmExpanded: false,
    awaitingExpansion: false, // True when choosing an edge arrow to expand the overworld
    totalKills: 0,
    totalShardsEarned: 150,

    playSound: function (soundName, param) {
      SoundManager.play(soundName, param);
    },

    // State Mutation Methods
    addShards: function (amount) {
      this.shards += amount;
      updateHud();
    },

    addEssence: function (amount) {
      this.essence += amount;
      this.playSound('essenceGain');
      updateHud();
    },

    damageSanctum: function (amount) {
      if (this.gameOver) return;
      this.sanctumHp = Math.max(0, this.sanctumHp - amount);

      // Trigger red screen damage flash
      if (this.vignetteEnabled) {
        damageVignetteTimer = 0.15;
        const vig = document.getElementById('damage-vignette');
        if (vig) vig.classList.add('hit');
      }
      sanctumHitTimer = 0.35;

      const hpBar = document.getElementById('hud-hp-bar');
      if (hpBar) {
        hpBar.classList.add('flash');
        setTimeout(() => hpBar.classList.remove('flash'), 180);
      }

      // Flash Sanctum eyes angry red
      sanctumEyes.forEach(eye => {
        eye.material = getMat(C.GLOW_RED, C.GLOW_RED, 2.5);
      });

      this.playSound('sanctumDamage');
      updateHud();

      if (this.sanctumHp <= 0) {
        this.triggerDefeat();
      }
    },

    selectGolemType: function (type) {
      this.selectedGolemType = type;
      document.querySelectorAll('.golem-card').forEach(card => {
        card.classList.toggle('active', card.getAttribute('data-type') === type);
      });
      updateRangeRingPreview();
    },

    selectPedestal: function (pedestal) {
      this.selectedPedestal = pedestal;
      if (pedestal && pedestal.golem) {
        this.selectedGolem = pedestal.golem;
        openGolemInspector(pedestal.golem);
        showRangeRing(pedestal.golem.position, pedestal.golem.range, pedestal.golem.config.color);
      } else {
        this.selectedGolem = null;
        closeGolemInspector();
        hideRangeRing();
      }
    },

    deselect: function () {
      this.selectedPedestal = null;
      this.selectedGolem = null;
      closeGolemInspector();
      hideRangeRing();
    },

    toggleSpeed: function () {
      if (this.gameSpeed === 1.0) {
        this.gameSpeed = 2.0;
      } else if (this.gameSpeed === 2.0) {
        this.gameSpeed = 4.0;
      } else {
        this.gameSpeed = 1.0;
      }
      updateHud();
    },

    startNextWave: function () {
      if (this.awaitingExpansion) {
        FloatingTextManager.spawnText(cameraTarget.clone().add(new THREE.Vector3(0, 2, 0)), 'CHOOSE AN EDGE ARROW TO EXPAND THE REALM!', 'dmg-crit');
        this.playSound('error');
        return;
      }
      if (this.waveActive || this.gameOver) return;
      if (!this.endlessMode && this.currentWave >= this.totalWaves) return;

      this.currentWave++;
      this.waveActive = true;
      WaveManager.startWave(this.currentWave);
      updateHud();
      this.playSound('waveStart');
    },

    onWaveComplete: function () {
      this.waveActive = false;
      const bonus = 25 + (this.currentWave * 10);
      this.addShards(bonus);
      this.playSound('upgrade');

      if (this.currentWave % 10 === 0 && !this.gameOver) {
        ChunkManager.showExpansionPrompt();
      } else {
        updateHud();
      }
    },

    triggerVictory: function () {
      this.gameWon = true;
      const modal = document.getElementById('modal-victory');
      if (modal) {
        modal.classList.remove('hidden');
        const killsEl = document.getElementById('vic-kills');
        const shardsEl = document.getElementById('vic-shards');
        const hpEl = document.getElementById('vic-hp');
        if (killsEl) killsEl.textContent = `${this.totalKills}`;
        if (shardsEl) shardsEl.textContent = `${this.totalShardsEarned} 💎`;
        if (hpEl) hpEl.textContent = `${this.sanctumHp} / ${this.maxSanctumHp}`;
      }
      this.playSound('victory');
      updateHud();
    },

    triggerDefeat: function () {
      this.gameOver = true;
      const modal = document.getElementById('modal-gameover');
      if (modal) {
        modal.classList.remove('hidden');
        const waveEl = document.getElementById('def-wave');
        const killsEl = document.getElementById('def-kills');
        if (waveEl) waveEl.textContent = `Wave ${this.currentWave}`;
        if (killsEl) killsEl.textContent = `${this.totalKills}`;
      }
      // Turn Sanctum eyes dim red
      sanctumEyes.forEach(eye => {
        eye.material = getMat(C.GLOW_RED, C.GLOW_RED, 1.0);
      });
      this.playSound('defeat');
      updateHud();

      // Auto-restart countdown (8 seconds) with instant skip on click
      let countdown = 8;
      const btnDefReset = document.getElementById('btn-defeat-reset');
      if (btnDefReset) {
        btnDefReset.textContent = `⚔️ NEW REALM IN (${countdown}s)`;
      }
      if (this.defeatInterval) clearInterval(this.defeatInterval);
      this.defeatInterval = setInterval(() => {
        countdown--;
        if (btnDefReset) {
          btnDefReset.textContent = countdown > 0
            ? `⚔️ NEW REALM IN (${countdown}s)`
            : `⚔️ GENERATING REALM...`;
        }
        if (countdown <= 0) {
          clearInterval(this.defeatInterval);
          this.defeatInterval = null;
          resetGame();
        }
      }, 1000);
    }
  };

  // Expose to window for Phase 3 binding
  window.GameState = GameState;

  // ========================================================
  // GLOBAL THREE.JS SCENE STATE
  // ========================================================
  var scene, camera, renderer, clock;
  var cameraTarget = new THREE.Vector3(7.5, 1.5, 7.5);
  var targetCameraPos = new THREE.Vector3(7.5, 1.5, 7.5);
  var cameraZoom = 10.5;
  var targetZoom = 10.5;

  var pedestals = [];
  var activeGolems = [];
  var activeEnemies = [];
  var activeProjectiles = [];
  var activeParticles = [];
  var activeBeams = [];
  var activeSlamRings = [];
  var activeTornadoes = [];

  var hoveredPedestal = null;
  var rangeRingMesh = null;
  var rangeRingPreviewMesh = null;

  var waterfallFlow = [];
  var waterfallFoam = [];
  var oasisWater = [];
  var environmentalProps = []; // Interactive and wind-reactive environmental assets
  var sandRoughnessMap = null; // Procedural 32x32 retro pixel roughness texture
  var sanctumEyes = [];
  var sanctumLight = null;
  var portalRunes = [];
  var damageVignetteTimer = 0;
  var sanctumHitTimer = 0;

  var raycaster = new THREE.Raycaster();
  var mouse = new THREE.Vector2();

  var sandRoughnessMapL1 = null; // Subtle fringe roughness
  var sandRoughnessMapL2 = null; // Core patch center roughness
  var ditherTextureCache = new Map();

  // Standard 8x8 Bayer Matrix for seamless retro ordered pixel dithering
  const BAYER_8x8 = [
    [ 0, 32,  8, 40,  2, 34, 10, 42],
    [48, 16, 56, 24, 50, 18, 58, 26],
    [12, 44,  4, 36, 14, 46,  6, 38],
    [60, 28, 52, 20, 62, 30, 54, 22],
    [ 3, 35, 11, 43,  1, 33,  9, 41],
    [51, 19, 59, 27, 49, 17, 57, 25],
    [15, 47,  7, 39, 13, 45,  5, 37],
    [63, 31, 55, 23, 61, 29, 53, 21]
  ];

  // Active procedural rough sand patches (distributed randomly across the map, not static/centered)
  var activeRoughPatches = [];

  function generateRoughPatchesForChunk(cx, cz) {
    const originX = cx * 16;
    const originZ = cz * 16;
    // 50% chance of 1 medium/large patch, 50% chance of 2 distinct patches
    const count = Math.random() < 0.5 ? 1 : 2;

    // Candidate sector zones across the 16x16 chunk to guarantee variety and avoid centering:
    // NW, NE, SW, SE, North-central, South-central, East-central, West-central
    const zones = [
      { x: 3.5,  z: 4.0 },  // NW (near cliffside / cascade)
      { x: 12.0, z: 4.0 },  // NE (northeast dunes)
      { x: 4.0,  z: 11.5 }, // SW (southwest slope)
      { x: 11.5, z: 12.0 }, // SE (southeast dunes)
      { x: 8.0,  z: 3.2 },  // North dunes
      { x: 8.0,  z: 12.8 }, // South perimeter ridge
      { x: 12.8, z: 8.0 },  // East mesa
      { x: 3.2,  z: 8.0 }   // West canyon
    ];

    // Fisher-Yates shuffle
    for (let i = zones.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [zones[i], zones[j]] = [zones[j], zones[i]];
    }

    for (let i = 0; i < count; i++) {
      const z = zones[i];
      const px = originX + z.x + (Math.random() - 0.5) * 2.2;
      const pz = originZ + z.z + (Math.random() - 0.5) * 2.2;
      const rx = (count === 1) ? (2.8 + Math.random() * 1.2) : (2.0 + Math.random() * 0.9);
      const rz = (count === 1) ? (2.4 + Math.random() * 1.0) : (1.8 + Math.random() * 0.8);
      activeRoughPatches.push({
        x: px,
        z: pz,
        radiusX: rx,
        radiusZ: rz,
        rotation: Math.random() * Math.PI,
        noisePhase1: Math.random() * Math.PI * 2,
        noisePhase2: Math.random() * Math.PI * 2,
        intensityPeak: 0.93 + Math.random() * 0.08
      });
    }
  }

  // Pre-seed initial chunk (0, 0) patches
  generateRoughPatchesForChunk(0, 0);

  // Continuous spatial roughness scalar field across world coordinates
  // Samples distance to procedurally randomized patch centers with organic boundary noise
  function getRoughnessScalar(wx, wz) {
    if (activeRoughPatches.length === 0) {
      return 0.5; // Baseline smooth sandstone if no patches exist
    }
    let maxScalar = 0.5;

    for (let i = 0; i < activeRoughPatches.length; i++) {
      const patch = activeRoughPatches[i];
      const dx = wx - patch.x;
      const dz = wz - patch.z;

      // Fast bounding-box rejection
      const maxR = Math.max(patch.radiusX, patch.radiusZ) * 1.5;
      if (Math.abs(dx) > maxR || Math.abs(dz) > maxR) continue;

      const cos = Math.cos(patch.rotation);
      const sin = Math.sin(patch.rotation);
      const rx = dx * cos - dz * sin;
      const rz = dx * sin + dz * cos;
      const normDistSq = (rx / patch.radiusX) * (rx / patch.radiusX) + (rz / patch.radiusZ) * (rz / patch.radiusZ);

      // Multi-frequency organic boundary noise
      const organicNoise = Math.sin(wx * 0.9 + patch.noisePhase1) * 0.18 + Math.cos(wz * 0.85 + patch.noisePhase2) * 0.18;
      const effDist = Math.sqrt(normDistSq) + organicNoise;

      if (effDist < 1.0) {
        const factor = Math.max(0.0, 1.0 - effDist);
        // Intensity scales smoothly from 0.64 (outer edge) up to intensityPeak (deep core)
        const scalar = 0.64 + factor * (patch.intensityPeak - 0.64);
        if (scalar > maxScalar) maxScalar = scalar;
      }
    }

    return maxScalar;
  }

  // Returns 0 (Clean smooth sandstone), 1 (Fringe dither transition), 2 (Core rougher center)
  function getTileRoughnessLevel(wx, wz) {
    const v = getRoughnessScalar(wx + 0.5, wz + 0.5);
    if (v > 0.80) return 2; // Core rougher center (surrounded by roughness)
    if (v > 0.66) return 1; // Subtle outer dither transition zone
    return 0;               // Clean smooth sandstone ground
  }

  // Procedural retro voxel ordered dither texture generator
  // Seamlessly dissolves rough patches into the normal ground texture (#FFD166) across tile borders
  function getSandDitherTexture(wx, wz) {
    const lvl = getTileRoughnessLevel(wx, wz);
    if (lvl === 0) {
      // Check if any corner reaches into the dither zone (> 0.66)
      const vNW = getRoughnessScalar(wx, wz);
      const vNE = getRoughnessScalar(wx + 1, wz);
      const vSW = getRoughnessScalar(wx, wz + 1);
      const vSE = getRoughnessScalar(wx + 1, wz + 1);
      if (Math.max(vNW, vNE, vSW, vSE) <= 0.66) {
        return null; // 100% clean solid sandstone tile, zero texture overhead
      }
    }

    const cacheKey = `${wx},${wz}`;
    if (ditherTextureCache.has(cacheKey)) {
      return ditherTextureCache.get(cacheKey);
    }

    const size = 16;
    const canvas = document.createElement('canvas');
    canvas.width = size;
    canvas.height = size;
    const ctx = canvas.getContext('2d');

    // 1. Base color: clean vibrant sandstone (#FFD166) matching normal ground
    ctx.fillStyle = '#FFD166';
    ctx.fillRect(0, 0, size, size);

    // 2. Sample continuous world-pixel space & apply Bayer ordered dithering
    for (let py = 0; py < size; py++) {
      for (let px = 0; px < size; px++) {
        const worldX = wx + (px + 0.5) / size;
        const worldZ = wz + (py + 0.5) / size;
        const v = getRoughnessScalar(worldX, worldZ);

        if (v > 0.66) {
          // Normalized roughness gradient from edge (0.0) to deep center core (1.0)
          const intensity = Math.min(1.0, (v - 0.66) / 0.18);
          const gx = Math.floor(wx * size + px);
          const gz = Math.floor(wz * size + py);
          const bayerRow = ((gz % 8) + 8) % 8;
          const bayerCol = ((gx % 8) + 8) % 8;
          const bayerThreshold = BAYER_8x8[bayerRow][bayerCol] / 64.0;

          if (intensity > bayerThreshold) {
            // Retro voxel pixel dither triggered!
            const h = (Math.abs(gx * 17 + gz * 31) % 100) / 100.0;

            if (intensity < 0.45) {
              // Outer subtle fringe: gentle warm golden transition
              ctx.fillStyle = h < 0.70 ? '#FAD062' : '#F6C756';
            } else if (intensity < 0.80) {
              // Mid roughness: warmer ochre & dune grit
              if (h < 0.55) ctx.fillStyle = '#F0BE48';
              else if (h < 0.85) ctx.fillStyle = '#E8B23C';
              else ctx.fillStyle = '#FFE28C'; // subtle quartz sparkle
            } else {
              // Deep center core (surrounded by roughness: maximum roughness)
              if (h < 0.45) ctx.fillStyle = '#EBB648';
              else if (h < 0.75) ctx.fillStyle = '#DF9E34'; // rich coarse ochre
              else if (h < 0.90) ctx.fillStyle = '#CF8424'; // weathered terracotta grain
              else ctx.fillStyle = '#FFE698';               // sunlit quartz crystal
            }
            ctx.fillRect(px, py, 1, 1);
          }
        }
      }
    }

    const tex = new THREE.CanvasTexture(canvas);
    tex.magFilter = THREE.NearestFilter;
    tex.minFilter = THREE.NearestFilter;
    tex.generateMipmaps = false;
    tex.wrapS = THREE.ClampToEdgeWrapping;
    tex.wrapT = THREE.ClampToEdgeWrapping;
    ditherTextureCache.set(cacheKey, tex);
    return tex;
  }

  // Backward-compatibility initialization
  function createSandRoughnessTextures() {
    if (activeRoughPatches.length > 0) {
      const p = activeRoughPatches[0];
      sandRoughnessMapL1 = getSandDitherTexture(Math.floor(p.x), Math.floor(p.z));
      sandRoughnessMapL2 = sandRoughnessMapL1;
    } else {
      sandRoughnessMapL1 = null;
      sandRoughnessMapL2 = null;
    }
    sandRoughnessMap = sandRoughnessMapL1;
  }

  function createSandRoughnessTexture() {
    createSandRoughnessTextures();
    return sandRoughnessMapL1;
  }

  // Shared geometry & material caches to prevent WebGL leaks
  var geoCache = {};
  var matCache = {};

  function getMat(color, emissive, emIntensity, opacity, map) {
    const key = `${color}_${emissive||0}_${emIntensity||0}_${opacity||1}_${map ? map.id : 0}`;
    if (!matCache[key]) {
      const opts = { color: color };
      if (emissive) {
        opts.emissive = emissive;
        opts.emissiveIntensity = emIntensity || 1.0;
      }
      if (opacity !== undefined && opacity < 1) {
        opts.transparent = true;
        opts.opacity = opacity;
      }
      if (map) {
        opts.map = map;
      }
      matCache[key] = new THREE.MeshLambertMaterial(opts);
    }
    return matCache[key];
  }

  function getGeo(w, h, d) {
    const key = `${w}_${h}_${d}`;
    if (!geoCache[key]) {
      geoCache[key] = new THREE.BoxGeometry(w, h, d);
    }
    return geoCache[key];
  }

  function vox(x, y, z, w, h, d, color, parent, emissive, emInt, opacity, map) {
    const mesh = new THREE.Mesh(getGeo(w, h, d), getMat(color, emissive, emInt, opacity, map));
    mesh.position.set(x, y, z);
    mesh.castShadow = true;
    mesh.receiveShadow = true;
    if (parent) parent.add(mesh);
    return mesh;
  }

  function isPathCell(x, z) {
    return pathSet.has(`${x},${z}`);
  }

  function getTerrainHeight(x, z) {
    const rx = Math.floor(x);
    const rz = Math.floor(z);
    if (isPathCell(rx, rz)) return 0.85;
    return heightMap.get(`${rx},${rz}`) || 1;
  }

  function getSandSurfaceColor(x, z) {
    const rx = Math.floor(x);
    const rz = Math.floor(z);
    // Spatial hash for natural micro-tonal variations across desert sand
    const h = Math.abs((Math.sin(rx * 12.9898 + rz * 78.233) * 43758.5453) % 1);
    if (h < 0.22) return 0xF5C75A; // Sun-drenched high ridge
    if (h < 0.46) return 0xF0C050; // Classic warm sandstone ochre
    if (h < 0.68) return 0xEAB646; // Weathered golden dune
    if (h < 0.86) return 0xE3AC3C; // Terracotta sand wash
    return 0xDB9F30;                // Coarse desert grit
  }

  function getTerrainColor(y, maxH, x, z, hasMap) {
    if (y === maxH) {
      if (hasMap) return 0xFFFFFF;
      return C.SAND_L; // Clean, bright, original solid sandstone #FFD166
    }
    if (y === maxH - 1) return C.SAND_M;
    if (y === maxH - 2) return C.SAND_D;
    return C.SAND_X;
  }

  // ========================================================
  // INITIALIZATION & LIGHTING
  // ========================================================

  function initScene() {
    scene = new THREE.Scene();
    scene.background = new THREE.Color(C.SKY);

    renderer = new THREE.WebGLRenderer({ antialias: false, powerPreference: 'high-performance' });
    renderer.setPixelRatio(1);
    renderer.setSize(
      Math.floor(window.innerWidth / PIXEL_SCALE),
      Math.floor(window.innerHeight / PIXEL_SCALE),
      false
    );
    renderer.outputEncoding = THREE.sRGBEncoding;
    renderer.shadowMap.enabled = true;
    renderer.shadowMap.type = THREE.PCFSoftShadowMap;

    document.getElementById('game-container').appendChild(renderer.domElement);

    const aspect = window.innerWidth / window.innerHeight;
    camera = new THREE.OrthographicCamera(
      -cameraZoom * aspect, cameraZoom * aspect,
      cameraZoom, -cameraZoom,
      -100, 300
    );
    updateCamera();

    clock = new THREE.Clock();
  }

  function updateCamera() {
    const aspect = window.innerWidth / window.innerHeight;
    camera.left   = -cameraZoom * aspect;
    camera.right  =  cameraZoom * aspect;
    camera.top    =  cameraZoom;
    camera.bottom = -cameraZoom;
    camera.updateProjectionMatrix();

    const isoDir = new THREE.Vector3(1, 1, 1).normalize().multiplyScalar(70);
    camera.position.copy(cameraTarget).add(isoDir);
    camera.lookAt(cameraTarget);
  }

  function setupLighting() {
    const sun = new THREE.DirectionalLight(0xFFF1D0, 1.45);
    sun.position.set(24, 38, 20);
    sun.target.position.set(7.5, 0, 7.5);
    sun.castShadow = true;

    sun.shadow.mapSize.width = 2048;
    sun.shadow.mapSize.height = 2048;
    sun.shadow.camera.left   = -20;
    sun.shadow.camera.right  =  20;
    sun.shadow.camera.top    =  20;
    sun.shadow.camera.bottom = -20;
    sun.shadow.camera.near   = 1;
    sun.shadow.camera.far    = 90;
    sun.shadow.bias = -0.0006;
    scene.add(sun);
    scene.add(sun.target);

    const skyFill = new THREE.DirectionalLight(0x7EC8E3, 0.4);
    skyFill.position.set(-15, 20, -10);
    scene.add(skyFill);

    const ambient = new THREE.AmbientLight(0xFFE8C8, 0.42);
    scene.add(ambient);

    const hemi = new THREE.HemisphereLight(0xFFF8E7, 0x8C5E35, 0.35);
    scene.add(hemi);
  }

  // ========================================================
  // PROCEDURAL TERRAIN BUILDERS & SANCTUM
  // ========================================================

  function buildPortalMesh(x, y, z) {
    const portalGroup = new THREE.Group();
    portalGroup.position.set(x, y, z);
    vox(-0.55, 1.2, 0, 0.35, 2.4, 0.4, C.STN_D, portalGroup);
    vox( 0.55, 1.2, 0, 0.35, 2.4, 0.4, C.STN_D, portalGroup);
    vox(-0.55, 2.5, 0, 0.45, 0.25, 0.5, C.STN_L, portalGroup);
    vox( 0.55, 2.5, 0, 0.45, 0.25, 0.5, C.STN_L, portalGroup);
    vox(0, 2.7, 0, 1.6, 0.35, 0.45, C.STN_M, portalGroup);
    vox(0, 3.0, 0, 0.8, 0.3, 0.4, C.STN_L, portalGroup);

    const portalMesh = vox(0, 1.3, 0, 0.85, 2.2, 0.08, 0xCC3333, portalGroup, 0xCC2222, 1.5, 0.85);
    portalRunes.push(portalMesh);
    const circleMesh = vox(0, 0.04, 0, 1.1, 0.04, 1.1, 0xCC3333, portalGroup, 0xCC2222, 1.0);
    portalRunes.push(circleMesh);
    return portalGroup;
  }

  function createPedestalMesh(id, x, y, z) {
    const g = new THREE.Group();
    g.position.set(x, y, z);

    // Plinth base
    vox(0, 0.15, 0, 1.1, 0.3, 1.1, C.PED_BASE, g);
    vox(0, 0.4,  0, 0.92, 0.25, 0.92, C.PED_TOP, g);
    vox(0, 0.58, 0, 0.98, 0.12, 0.98, C.PED_BASE, g);

    // Glowing rune ring on top
    const runeMesh = vox(0, 0.65, 0, 0.72, 0.03, 0.72, C.PED_RUNE, g, C.PED_RUNE, 0.8);
    vox(0, 0.66, 0, 0.48, 0.03, 0.48, C.PED_TOP, g);

    // Corner pillars
    const cp = 0.42;
    [[-cp,-cp],[cp,-cp],[-cp,cp],[cp,cp]].forEach(c => {
      vox(c[0], 0.35, c[1], 0.18, 0.65, 0.18, C.STN_M, g);
      vox(c[0], 0.7,  c[1], 0.12, 0.1,  0.12, C.PED_RUNE, g, C.PED_RUNE, 0.6);
    });

    // Glowing Vertical Rune Beacon (Guarantees Pedestal Visibility Across Any Distance!)
    const beaconGroup = new THREE.Group();
    const beamGeo = new THREE.CylinderGeometry(0.05, 0.05, 2.4, 8);
    const beamMat = new THREE.MeshBasicMaterial({
      color: 0x39FF14,
      transparent: true,
      opacity: 0.32,
      depthWrite: false,
      side: THREE.DoubleSide
    });
    const beamMesh = new THREE.Mesh(beamGeo, beamMat);
    beamMesh.position.set(0, 1.85, 0);
    beaconGroup.add(beamMesh);

    // Rotating diamond beacon prism at apex
    const diamondPrism = vox(0, 3.0, 0, 0.2, 0.2, 0.2, C.PED_RUNE, beaconGroup, C.PED_RUNE, 2.2);
    diamondPrism.rotation.y = Math.PI / 4;
    diamondPrism.rotation.z = Math.PI / 4;
    beaconGroup.userData.diamond = diamondPrism;
    beaconGroup.userData.beam = beamMesh;
    g.add(beaconGroup);

    // Clickable collider box for raycaster
    const colGeo = new THREE.BoxGeometry(1.2, 1.2, 1.2);
    const colMat = new THREE.MeshBasicMaterial({ visible: false });
    const collider = new THREE.Mesh(colGeo, colMat);
    collider.position.set(0, 0.6, 0);
    g.add(collider);

    const pedObj = {
      id: id,
      x: x,
      z: z,
      y: y,
      group: g,
      runeMesh: runeMesh,
      collider: collider,
      beaconGroup: beaconGroup,
      golem: null
    };

    collider.userData.pedestal = pedObj;
    return pedObj;
  }

  function buildSanctum(x = 2.5, y = 1.0, z = 2.5, rotY = Math.PI * 0.25) {
    const sanctumGroup = new THREE.Group();
    sanctumGroup.position.set(x, y, z);

    // Backing sandstone cliff behind monolith (mesa backdrop)
    vox(-1.8, 2.5,  0.0, 2.6, 5.2, 3.8, C.SAND_X, sanctumGroup);
    vox(-1.2, 2.0, -1.2, 2.0, 4.0, 2.0, C.SAND_D, sanctumGroup);
    vox(-1.2, 2.0,  1.2, 2.0, 4.0, 2.0, C.SAND_D, sanctumGroup);
    vox(-1.5, 4.8,  0.0, 2.0, 3.0, 3.2, C.SAND_M, sanctumGroup);

    vox(0, 1.5, 0, 3.8, 3.0, 2.8, C.STN_D, sanctumGroup);
    vox(0, 2.8, 0.8, 3.2, 1.8, 1.6, C.STN_M, sanctumGroup);
    vox(-2.2, 3.0, 0.2, 1.2, 2.4, 2.2, C.STN_M, sanctumGroup);
    vox( 2.2, 3.0, 0.2, 1.2, 2.4, 2.2, C.STN_M, sanctumGroup);

    // Mouth cavern entrance
    vox(0, 1.2, 1.0, 1.8, 2.4, 1.8, 0x0A0908, sanctumGroup);
    vox(0, 2.45, 1.6, 2.2, 0.45, 0.6, C.STN_D, sanctumGroup);
    vox(0, 0.15, 1.6, 2.2, 0.3, 0.6, C.STN_X, sanctumGroup);
    vox(-0.9, 0.7, 1.6, 0.35, 0.9, 0.35, C.STN_L, sanctumGroup);
    vox( 0.9, 0.7, 1.6, 0.35, 0.9, 0.35, C.STN_L, sanctumGroup);

    // Head
    const headCenterY = 5.2;
    vox(0, headCenterY, 0.2, 3.4, 2.8, 2.8, C.STN_M, sanctumGroup);
    vox(0, headCenterY + 0.8, 1.6, 3.6, 0.65, 0.8, C.STN_D, sanctumGroup);
    vox(-1.4, headCenterY - 0.2, 1.3, 0.65, 0.9, 0.8, C.STN_D, sanctumGroup);
    vox( 1.4, headCenterY - 0.2, 1.3, 0.65, 0.9, 0.8, C.STN_D, sanctumGroup);
    vox(0, headCenterY + 0.1, 1.7, 0.65, 1.1, 0.5, C.STN_L, sanctumGroup);
    vox(-0.8, headCenterY + 0.5, 1.55, 0.8, 0.6, 0.4, 0x0D0D0D, sanctumGroup);
    vox( 0.8, headCenterY + 0.5, 1.55, 0.8, 0.6, 0.4, 0x0D0D0D, sanctumGroup);

    const eyeL = vox(-0.8, headCenterY + 0.5, 1.76, 0.55, 0.45, 0.12, C.GLOW_GRN, sanctumGroup, C.GLOW_GRN, 1.8);
    const eyeR = vox( 0.8, headCenterY + 0.5, 1.76, 0.55, 0.45, 0.12, C.GLOW_GRN, sanctumGroup, C.GLOW_GRN, 1.8);
    sanctumEyes.push(eyeL, eyeR);

    sanctumLight = new THREE.PointLight(0x39FF14, 1.4, 6.5);
    sanctumLight.position.set(0, headCenterY + 0.5, 2.2);
    sanctumGroup.add(sanctumLight);

    vox(0, headCenterY + 1.6, 0.2, 2.8, 0.5, 2.4, C.STN_D, sanctumGroup);
    // Face directly into the player's isometric camera!
    sanctumGroup.rotation.y = rotY;
    scene.add(sanctumGroup);
    return sanctumGroup;
  }

  function buildWaterfallAndOasis(parent, cliffX = 1.0, cliffZ = 4.0) {
    const waterGroup = new THREE.Group();
    const cascadeSteps = [
      { x: cliffX, z: cliffZ, yTop: 3.5, yBot: 2.2 },
      { x: cliffX + 0.5, z: cliffZ + 0.6, yTop: 2.2, yBot: 1.1 }
    ];
    cascadeSteps.forEach(step => {
      const h = step.yTop - step.yBot;
      const fall = vox(step.x, step.yBot + h/2, step.z, 0.8, h, 0.2, C.WAT_M, waterGroup, C.WAT_M, 0.3, 0.9);
      fall.userData.baseY = fall.position.y;
      waterfallFlow.push(fall);
      const foam = vox(step.x, step.yBot + 0.1, step.z + 0.15, 0.9, 0.14, 0.3, C.WAT_FOAM, waterGroup, C.WAT_FOAM, 0.8);
      foam.userData.baseY = foam.position.y;
      waterfallFoam.push(foam);
    });

    for (let ox = cliffX; ox <= cliffX + 2; ox++) {
      for (let oz = cliffZ + 1; oz <= cliffZ + 3; oz++) {
        if (isPathCell(ox, oz)) continue;
        const k = `${ox},${oz}`;
        if (terrainMeshesByCell.has(k)) {
          const list = terrainMeshesByCell.get(k);
          for (let i = list.length - 1; i >= 0; i--) {
            if (list[i].position.y >= 0.4) {
              if (list[i].parent) list[i].parent.remove(list[i]);
              list.splice(i, 1);
            }
          }
        }
        vox(ox, 0.35, oz, 1.0, 0.15, 1.0, C.SAND_D, waterGroup);
        const poolW = vox(ox, 0.70, oz, 0.98, 0.08, 0.98, C.WAT_M, waterGroup, C.WAT_M, 0.3, 0.92);
        poolW.userData.baseY = 0.70;
        oasisWater.push(poolW);
      }
    }

    parent.add(waterGroup);
    return waterGroup;
  }

  function buildProceduralDecorations(parent, cx, cz, extraAvoidPortal = null) {
    const originX = cx * 16;
    const originZ = cz * 16;
    const created = [];

    // 1. Identify all valid candidate cells in this 16x16 chunk
    const candidates = [];
    for (let lx = 0; lx < 16; lx++) {
      for (let lz = 0; lz < 16; lz++) {
        const wx = originX + lx;
        const wz = originZ + lz;

        // Path constraint: props must NEVER spawn on path tiles
        if (isPathCell(wx, wz)) continue;

        // Pedestal constraint: never on pedestal or within 1-tile clearance radius
        const nearPedestal = pedestals.some(p => Math.abs(p.x - wx) <= 1 && Math.abs(p.z - wz) <= 1);
        if (nearPedestal) continue;

        // Sanctum & Waterfall clearance on base chunk (0, 0)
        if (cx === 0 && cz === 0) {
          if (wx <= 4 && wz <= 7) continue;
        }

        // Portal zones clearance (starting portal & active invasion portals)
        let nearPortal = false;
        if (startingPortalGroup && cx === 0 && cz === 0) {
          const spX = WAYPOINTS.length > 0 ? WAYPOINTS[0].x : 14;
          const spZ = WAYPOINTS.length > 0 ? WAYPOINTS[0].z : 2;
          if (Math.abs(spX - wx) <= 1 && Math.abs(spZ - wz) <= 1) nearPortal = true;
        }
        if (!nearPortal && ChunkManager && ChunkManager.activePortals) {
          for (const port of ChunkManager.activePortals) {
            if (port.pos && Math.abs(port.pos.x - wx) <= 1 && Math.abs(port.pos.z - wz) <= 1) {
              nearPortal = true;
              break;
            }
          }
        }
        if (!nearPortal && extraAvoidPortal) {
          if (Math.abs(extraAvoidPortal.x - wx) <= 1 && Math.abs(extraAvoidPortal.z - wz) <= 1) {
            nearPortal = true;
          }
        }
        if (nearPortal) continue;

        candidates.push({ lx, lz, wx, wz });
      }
    }

    if (candidates.length === 0) return created;

    const candidateSet = new Set(candidates.map(c => `${c.wx},${c.wz}`));
    const placedSet = new Set();
    const placedPositions = [];

    // Footprint check for multi-tile structures
    function canFitFootprint(startX, startZ, w, d, reqElev = null) {
      for (let dx = 0; dx < w; dx++) {
        for (let dz = 0; dz < d; dz++) {
          const wx = startX + dx;
          const wz = startZ + dz;
          const k = `${wx},${wz}`;
          if (!candidateSet.has(k)) return false;
          if (placedSet.has(k)) return false;
          if (reqElev !== null && getTerrainHeight(wx, wz) !== reqElev) return false;
          // Spacing buffer from other placed objects
          for (let i = 0; i < placedPositions.length; i++) {
            const [px, pz] = placedPositions[i];
            if (Math.hypot(px - wx, pz - wz) < 1.45) return false;
          }
        }
      }
      return true;
    }

    // Excavate underlying ground for sunken structures (e.g. sunken oasis pool)
    function hollowBasin(startX, startZ, w, d) {
      for (let dx = 0; dx < w; dx++) {
        for (let dz = 0; dz < d; dz++) {
          const k = `${startX + dx},${startZ + dz}`;
          if (terrainMeshesByCell.has(k)) {
            const list = terrainMeshesByCell.get(k);
            for (let i = list.length - 1; i >= 0; i--) {
              if (list[i].position.y >= 0.4) {
                if (list[i].parent) list[i].parent.remove(list[i]);
                list.splice(i, 1);
              }
            }
          }
        }
      }
    }

    // Spawn a palm tree on dry sand beside the oasis perimeter
    function spawnPalmBesideOasis(parent, startX, startZ, w, d) {
      const neighbors = [
        { x: startX - 1, z: startZ },
        { x: startX + w, z: startZ },
        { x: startX, z: startZ - 1 },
        { x: startX, z: startZ + d },
        { x: startX - 1, z: startZ + 1 },
        { x: startX + w, z: startZ + 1 },
        { x: startX + 1, z: startZ - 1 },
        { x: startX + 1, z: startZ + d }
      ];
      for (const n of neighbors) {
        const k = `${n.x},${n.z}`;
        if (candidateSet.has(k) && !placedSet.has(k) && (heightMap.get(k) || 1) === 1) {
          const palm = TerrainAssetLibrary.spawnPalmTree(parent, n.x, 1, n.z);
          palm.userData.decorType = 'palm';
          palm.userData.chunkCoords = { cx, cz };
          palm.userData.worldCoords = { wx: n.x, wz: n.z };
          placedSet.add(k);
          placedPositions.push([n.x, n.z]);
          registerDecor(n.x, n.z, palm);
          created.push(palm);
          tallCount++;
          return palm;
        }
      }
      return null;
    }

    // Reserve all tiles of a footprint
    function reserveFootprint(obj, startX, startZ, w, d, typeName) {
      obj.userData.decorType = typeName;
      obj.userData.chunkCoords = { cx, cz };
      obj.userData.worldCoords = { wx: startX, wz: startZ };
      obj.userData.width = w;
      obj.userData.depth = d;
      created.push(obj);
      for (let dx = 0; dx < w; dx++) {
        for (let dz = 0; dz < d; dz++) {
          const wx = startX + dx;
          const wz = startZ + dz;
          placedSet.add(`${wx},${wz}`);
          placedPositions.push([wx, wz]);
          registerDecor(wx, wz, obj);
        }
      }
    }

    // 2. Budgeting & Category Limits
    // Environmental asset budget: 14–18 tiles/assets covered per chunk
    const budget = Math.floor(Math.random() * 5) + 14;

    let ruinsCount = 0;
    let tallCount = 0;
    let oasisCount = 0;
    let fossilCount = 0;

    // Shuffle candidate cells randomly (Fisher-Yates)
    const shuffled = [...candidates];
    for (let i = shuffled.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      const temp = shuffled[i];
      shuffled[i] = shuffled[j];
      shuffled[j] = temp;
    }

    // ----------------------------------------------------
    // PHASE 1: STRUCTURED MULTI-TILE LANDMARKS (Coherent Biomes)
    // ----------------------------------------------------

    // A. Grand Oasis Lagoon (Rare / Unique Landmark: ~35% chance per chunk, if none exists)
    const shouldRollOasis = Math.random() < 0.35;
    if (shouldRollOasis && oasisCount < 1) {
      for (const cell of shuffled) {
        const { wx, wz } = cell;
        const y = getTerrainHeight(wx, wz);
        if (y !== 1) continue; // Oasis belongs in low ground

        // Try 3x2 first, then 2x2
        if (canFitFootprint(wx, wz, 3, 2, 1)) {
          hollowBasin(wx, wz, 3, 2);
          const grandOasis = TerrainAssetLibrary.spawnGrandOasis(parent, wx, 1, wz, 3, 2);
          reserveFootprint(grandOasis, wx, wz, 3, 2, 'grand_oasis');
          oasisCount++;
          spawnPalmBesideOasis(parent, wx, wz, 3, 2);
          break;
        } else if (canFitFootprint(wx, wz, 2, 2, 1)) {
          hollowBasin(wx, wz, 2, 2);
          const grandOasis = TerrainAssetLibrary.spawnGrandOasis(parent, wx, 1, wz, 2, 2);
          reserveFootprint(grandOasis, wx, wz, 2, 2, 'grand_oasis');
          oasisCount++;
          spawnPalmBesideOasis(parent, wx, wz, 2, 2);
          break;
        }
      }
    }

    // B. Ancient Ruins Colonnade (2x2 or 2x1 temple plaza)
    if (ruinsCount < 1) {
      for (const cell of shuffled) {
        const { wx, wz } = cell;
        const y = getTerrainHeight(wx, wz);
        if (canFitFootprint(wx, wz, 2, 2, y)) {
          const ruins = TerrainAssetLibrary.spawnAncientRuinColonnade(parent, wx, y, wz, 2, 2);
          reserveFootprint(ruins, wx, wz, 2, 2, 'ancient_ruins');
          ruinsCount++;
          break;
        } else if (canFitFootprint(wx, wz, 2, 1, y)) {
          const ruins = TerrainAssetLibrary.spawnAncientRuinColonnade(parent, wx, y, wz, 2, 1);
          reserveFootprint(ruins, wx, wz, 2, 1, 'ancient_ruins');
          ruinsCount++;
          break;
        }
      }
    }

    // C. Mesa Hoodoo Ridge (2x1 stratified rock column)
    if (tallCount < 2) {
      for (const cell of shuffled) {
        const { lx, lz, wx, wz } = cell;
        const isPerimeter = (lx <= 1 || lx >= 14 || lz <= 1 || lz >= 14);
        const y = getTerrainHeight(wx, wz);
        if ((isPerimeter || y >= 2) && canFitFootprint(wx, wz, 2, 1, y)) {
          const ridge = TerrainAssetLibrary.spawnMesaHoodooRidge(parent, wx, y, wz, 2, 1);
          reserveFootprint(ridge, wx, wz, 2, 1, 'hoodoo_ridge');
          tallCount++;
          break;
        }
      }
    }

    // D. Desert Flora Cluster (2x1 acacia + prickly pear & tumbleweed shade cluster)
    if (tallCount < 2) {
      for (const cell of shuffled) {
        const { wx, wz } = cell;
        const y = getTerrainHeight(wx, wz);
        if (canFitFootprint(wx, wz, 2, 1, y)) {
          const cluster = TerrainAssetLibrary.spawnDesertFloraCluster(parent, wx, y, wz, 2, 1);
          reserveFootprint(cluster, wx, wz, 2, 1, 'flora_cluster');
          tallCount++;
          break;
        }
      }
    }

    // ----------------------------------------------------
    // PHASE 2: CLUSTERED SINGLE-TILE ACCENTS & FILLERS
    // ----------------------------------------------------
    for (const cell of shuffled) {
      if (placedSet.size >= budget) break;

      const { lx, lz, wx, wz } = cell;
      if (placedSet.has(`${wx},${wz}`)) continue;

      // Spacing check: 1.45 tiles between props
      const tooClose = placedPositions.some(([px, pz]) => Math.hypot(px - wx, pz - wz) < 1.45);
      if (tooClose) continue;

      const y = getTerrainHeight(wx, wz);

      const isPerimeter = (lx <= 1 || lx >= 14 || lz <= 1 || lz >= 14);
      const isHighGround = (y >= 2);
      const hasCliffStep = [
        { dx: 1, dz: 0 }, { dx: -1, dz: 0 }, { dx: 0, dz: 1 }, { dx: 0, dz: -1 }
      ].some(d => {
        const nh = heightMap.get(`${wx + d.dx},${wz + d.dz}`);
        return nh !== undefined && nh !== y;
      });

      const isPerimeterOrCliff = isPerimeter || isHighGround || hasCliffStep;
      const pool = [];

      if (isPerimeterOrCliff) {
        pool.push({ type: 'boulder_pile', weight: 30 });
        pool.push({ type: 'boulder_outcrop', weight: 16 });
        if (tallCount < 2) {
          pool.push({ type: 'hoodoo', weight: 20 });
          pool.push({ type: 'palm', weight: 24 });
          pool.push({ type: 'acacia', weight: 16 });
        }
        if (ruinsCount < 1) {
          pool.push({ type: 'broken_archway', weight: 14 });
        }
        if (hasCliffStep && !isPerimeter && y >= 2) {
          pool.push({ type: 'mini_waterfall', weight: 16 });
        }
        pool.push({ type: 'shrub', weight: 14 });
        pool.push({ type: 'saguaro_short', weight: 10 });
      } else {
        pool.push({ type: 'saguaro_norm', weight: 20 });
        if (tallCount < 2) {
          pool.push({ type: 'palm', weight: 28 });
          pool.push({ type: 'saguaro_tall', weight: 10 });
          pool.push({ type: 'acacia', weight: 10 });
        }
        pool.push({ type: 'prickly_pear', weight: 20 });
        pool.push({ type: 'barrel', weight: 18 });
        pool.push({ type: 'tumbleweed', weight: 20 });
        pool.push({ type: 'shrub', weight: 14 });
        pool.push({ type: 'pottery', weight: 12 });
        pool.push({ type: 'skeleton', weight: 10 });
        pool.push({ type: 'boulder_pile', weight: 10 });

        if (fossilCount < 1) {
          pool.push({ type: 'fossil_ribcage', weight: 10 });
        }

        if (y === 1 && !isPerimeter) {
          if (oasisCount < 1) {
            pool.push({ type: 'oasis', weight: 18 });
          }
          if (tallCount < 2) {
            pool.push({ type: 'palm', weight: 25 });
          }
          if (ruinsCount < 1) {
            pool.push({ type: 'runic_glyph', weight: 9 });
            pool.push({ type: 'broken_archway', weight: 6 });
          }
        }
      }

      if (pool.length === 0) continue;

      const totalWeight = pool.reduce((sum, item) => sum + item.weight, 0);
      let rand = Math.random() * totalWeight;
      let selected = pool[0].type;
      for (const item of pool) {
        if (rand < item.weight) {
          selected = item.type;
          break;
        }
        rand -= item.weight;
      }

      let decorObj = null;
      switch (selected) {
        case 'palm':
          decorObj = TerrainAssetLibrary.spawnPalmTree(parent, wx, y, wz);
          tallCount++;
          break;
        case 'mini_waterfall':
          decorObj = TerrainAssetLibrary.spawnMiniWaterfall(parent, wx, wz, y, 1);
          break;
        case 'saguaro_norm':
          decorObj = TerrainAssetLibrary.spawnSaguaro(parent, wx, y, wz, 3, Math.random() < 0.6 ? 1 : 0);
          break;
        case 'saguaro_short':
          decorObj = TerrainAssetLibrary.spawnSaguaro(parent, wx, y, wz, 2, 0);
          break;
        case 'saguaro_tall':
          decorObj = TerrainAssetLibrary.spawnSaguaro(parent, wx, y, wz, 4, 2);
          tallCount++;
          break;
        case 'prickly_pear':
          decorObj = TerrainAssetLibrary.spawnPricklyPear(parent, wx, y, wz);
          break;
        case 'acacia':
          decorObj = TerrainAssetLibrary.spawnAcaciaTree(parent, wx, y, wz);
          tallCount++;
          break;
        case 'tumbleweed':
          decorObj = TerrainAssetLibrary.spawnTumbleweedScrub(parent, wx, y, wz);
          break;
        case 'hoodoo':
          decorObj = TerrainAssetLibrary.spawnHoodooMesa(parent, wx, y, wz, 3);
          tallCount++;
          break;
        case 'boulder_pile':
          decorObj = TerrainAssetLibrary.spawnBoulderPile(parent, wx, y, wz);
          break;
        case 'boulder_outcrop':
          decorObj = TerrainAssetLibrary.spawnSandstoneOutcrop(parent, wx, y, wz, 1.0 + Math.random() * 0.3);
          break;
        case 'fossil_ribcage':
          decorObj = TerrainAssetLibrary.spawnFossilRibcage(parent, wx, y, wz);
          fossilCount++;
          break;
        case 'skeleton':
          decorObj = TerrainAssetLibrary.spawnSkeletonRemains(parent, wx, y, wz);
          break;
        case 'oasis':
          hollowBasin(wx, wz, 1, 1);
          decorObj = TerrainAssetLibrary.spawnOasisFeature(parent, wx, y, wz);
          oasisCount++;
          break;
        case 'broken_archway':
          decorObj = TerrainAssetLibrary.spawnBrokenArchway(parent, wx, y, wz);
          ruinsCount++;
          break;
        case 'pottery':
          decorObj = TerrainAssetLibrary.spawnPotteryUrns(parent, wx, y, wz);
          break;
        case 'runic_glyph':
          decorObj = TerrainAssetLibrary.spawnRunicGlyphTile(parent, wx, y, wz);
          ruinsCount++;
          break;
        case 'barrel':
          decorObj = TerrainAssetLibrary.spawnBarrelCactus(parent, wx, y, wz);
          break;
        case 'shrub':
        default:
          decorObj = TerrainAssetLibrary.spawnDesertShrub(parent, wx, y, wz);
          break;
      }

      if (decorObj) {
        reserveFootprint(decorObj, wx, wz, 1, 1, selected);
      }
    }

    // Ensure every sector features at least 1 palm tree
    const hasPalm = created.some(o => o.userData.decorType === 'palm');
    if (!hasPalm && tallCount < 2 && created.length > 0) {
      const replaceIdx = created.findIndex(o => o.userData.decorType === 'shrub' || o.userData.decorType === 'barrel');
      if (replaceIdx !== -1) {
        const oldObj = created[replaceIdx];
        const wx = oldObj.userData.worldCoords.wx;
        const wz = oldObj.userData.worldCoords.wz;
        const y = getTerrainHeight(wx, wz);
        if (oldObj.parent) oldObj.parent.remove(oldObj);
        const oldK = `${wx},${wz}`;
        decorByCell.delete(oldK);
        const palmObj = TerrainAssetLibrary.spawnPalmTree(parent, wx, y, wz);
        palmObj.userData.decorType = 'palm';
        palmObj.userData.chunkCoords = { cx, cz };
        palmObj.userData.worldCoords = { wx, wz };
        registerDecor(wx, wz, palmObj);
        created[replaceIdx] = palmObj;
      }
    }

    return created;
  }

  // ========================================================
  // PROCEDURAL PEBBLE SYSTEM (Tiny decorative stones)
  // ========================================================
  const PEBBLE_COLORS = {
    grey:       [0x808080, 0x8C8C8C, 0x737373],
    light_grey: [0xB8B8B8, 0xC8C8C8, 0xA8A8A8],
    brown:      [0x8B5A2B, 0x7A4B20, 0x966232],
    dark_brown: [0x4A2E12, 0x38200A, 0x563416],
    black:      [0x242424, 0x1A1A1A, 0x2E2E2E]
  };

  const PEBBLE_COLOR_KEYS = Object.keys(PEBBLE_COLORS);

  function getRandomPebbleColor() {
    const cat = PEBBLE_COLOR_KEYS[Math.floor(Math.random() * PEBBLE_COLOR_KEYS.length)];
    const shades = PEBBLE_COLORS[cat];
    return shades[Math.floor(Math.random() * shades.length)];
  }

  // Pool of procedural pebble shapes: small, deformed, round/faceted, longer, micro-cluster, flat flake
  function spawnTinyPebble(parent, x, y, z) {
    const g = new THREE.Group();
    g.position.set(x, y, z);
    g.userData.decorType = 'pebble';

    const shapeType = Math.floor(Math.random() * 6);
    const col = getRandomPebbleColor();
    const rotY = Math.random() * Math.PI * 2;

    switch (shapeType) {
      case 0: { // 1. Standard square stone (chunky block)
        const s = 0.12 + Math.random() * 0.04;
        const h = 0.042 + Math.random() * 0.014;
        const p = vox(0, h / 2, 0, s, h, s, col, g);
        p.rotation.y = rotY;
        break;
      }
      case 1: { // 2. Deformed / asymmetric angled stone
        const w = 0.17 + Math.random() * 0.04;
        const h = 0.048 + Math.random() * 0.014;
        const d = 0.11 + Math.random() * 0.03;
        const p = vox(0, h / 2, 0, w, h, d, col, g);
        p.rotation.y = rotY;
        p.rotation.z = (Math.random() - 0.5) * 0.15;
        break;
      }
      case 2: { // 3. Round / faceted cobble (stacked micro-voxels)
        const s = 0.14 + Math.random() * 0.03;
        const h1 = 0.032;
        const h2 = 0.024;
        vox(0, h1 / 2, 0, s, h1, s, col, g);
        const col2 = Math.random() < 0.6 ? col : getRandomPebbleColor();
        vox(0, h1 + h2 / 2, 0, s * 0.65, h2, s * 0.65, col2, g);
        g.rotation.y = rotY;
        break;
      }
      case 3: { // 4. Longer flat slate sliver
        const len = 0.22 + Math.random() * 0.05;
        const h = 0.038 + Math.random() * 0.012;
        const wid = 0.09 + Math.random() * 0.025;
        const p = vox(0, h / 2, 0, len, h, wid, col, g);
        p.rotation.y = rotY;
        break;
      }
      case 4: { // 5. Gravel pair (two distinct touching stones)
        const colB = getRandomPebbleColor();
        const h1 = 0.040;
        const h2 = 0.034;
        vox(-0.055, h1 / 2, 0, 0.085, h1, 0.08, col, g);
        vox( 0.055, h2 / 2, 0.025, 0.075, h2, 0.07, colB, g);
        g.rotation.y = rotY;
        break;
      }
      case 5: { // 6. Flat weathered shale slab
        const s = 0.18 + Math.random() * 0.04;
        const h = 0.030 + Math.random() * 0.010;
        const p = vox(0, h / 2, 0, s, h, s * 0.75, col, g);
        p.rotation.y = rotY;
        break;
      }
    }

    if (parent) parent.add(g);
    return g;
  }

  // Populate chunk surface with procedurally scattered, low-density pebbles (zero budget item cost)
  function populateChunkPebbles(parent, cx, cz) {
    const originX = cx * 16;
    const originZ = cz * 16;
    const pebbleGroup = new THREE.Group();
    pebbleGroup.userData.decorType = 'pebble_group';

    // 1. Gather all candidate open sand tiles
    const candidates = [];
    for (let lx = 0; lx < 16; lx++) {
      for (let lz = 0; lz < 16; lz++) {
        const wx = originX + lx;
        const wz = originZ + lz;
        const k = `${wx},${wz}`;

        // SAFETY: Never generate inside path tiles, decor items, pedestals, or portals
        if (isPathCell(wx, wz)) continue;
        if (decorByCell.has(k) && decorByCell.get(k).length > 0) continue;

        // Pedestal safety buffer
        if (pedestals.some(p => Math.abs(p.x - wx) <= 0.8 && Math.abs(p.z - wz) <= 0.8)) continue;

        // Sanctum base safety buffer on chunk (0, 0)
        if (cx === 0 && cz === 0 && wx <= 4 && wz <= 7) continue;

        // Portal safety buffer
        let nearPortal = false;
        if (startingPortalGroup && cx === 0 && cz === 0) {
          const spX = WAYPOINTS.length > 0 ? WAYPOINTS[0].x : 14;
          const spZ = WAYPOINTS.length > 0 ? WAYPOINTS[0].z : 2;
          if (Math.abs(spX - wx) <= 1 && Math.abs(spZ - wz) <= 1) nearPortal = true;
        }
        if (!nearPortal && ChunkManager && ChunkManager.activePortals) {
          for (const port of ChunkManager.activePortals) {
            if (port.pos && Math.abs(port.pos.x - wx) <= 1 && Math.abs(port.pos.z - wz) <= 1) {
              nearPortal = true;
              break;
            }
          }
        }
        if (nearPortal) continue;

        candidates.push({ wx, wz, groundY: heightMap.get(k) || 1 });
      }
    }

    // Shuffle candidate tiles for an organic, unbiased spatial distribution across the entire map
    for (let i = candidates.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [candidates[i], candidates[j]] = [candidates[j], candidates[i]];
    }

    // 2. Distribute low-density, broadly scattered pebbles with minimum spacing (no dense clumps)
    const placedPebbleCoords = [];
    const minSpacing = 2.1; // Ensure stones never clump together into dense clusters

    for (let cIdx = 0; cIdx < candidates.length; cIdx++) {
      const { wx, wz, groundY } = candidates[cIdx];

      // Minimum spacing check against already placed pebbles
      let tooClose = false;
      for (let i = 0; i < placedPebbleCoords.length; i++) {
        const [px, pz] = placedPebbleCoords[i];
        if (Math.hypot(px - wx, pz - wz) < minSpacing) {
          tooClose = true;
          break;
        }
      }
      if (tooClose) continue;

      // Low spawn probability (~28% of spaced candidate positions -> ~20-28 pebbles total per chunk)
      if (Math.random() < 0.28) {
        placedPebbleCoords.push([wx, wz]);

        // Predominantly single lone stones (88%), occasional small pair (12%)
        const count = Math.random() < 0.88 ? 1 : 2;

        for (let i = 0; i < count; i++) {
          let ox = (Math.random() - 0.5) * 0.52;
          let oz = (Math.random() - 0.5) * 0.52;
          // Keep safe buffer away from adjacent path tiles
          if (isPathCell(wx + 1, wz) && ox > 0.18) ox = 0.18;
          if (isPathCell(wx - 1, wz) && ox < -0.18) ox = -0.18;
          if (isPathCell(wx, wz + 1) && oz > 0.18) oz = 0.18;
          if (isPathCell(wx, wz - 1) && oz < -0.18) oz = -0.18;
          const p = spawnTinyPebble(pebbleGroup, wx + ox, groundY, wz + oz);
          registerDecor(wx, wz, p);
        }
      }
    }

    if (parent) parent.add(pebbleGroup);
    return pebbleGroup;
  }

  // ========================================================
  // GRID REGISTRY, DYNAMIC CARVING & PATH PRE-CALCULATION
  // ========================================================

  function registerTerrainVoxel(x, z, mesh) {
    const k = `${x},${z}`;
    if (!terrainMeshesByCell.has(k)) terrainMeshesByCell.set(k, []);
    terrainMeshesByCell.get(k).push(mesh);
  }

  function registerDecor(x, z, obj) {
    const k = `${x},${z}`;
    if (!decorByCell.has(k)) decorByCell.set(k, []);
    decorByCell.get(k).push(obj);
  }

  function registerPathMesh(x, z, mesh) {
    const k = `${x},${z}`;
    if (!pathMeshesByCell.has(k)) pathMeshesByCell.set(k, []);
    pathMeshesByCell.get(k).push(mesh);
  }

  function carveTileForPath(x, z, targetParent) {
    const k = `${x},${z}`;
    if (pathMeshesByCell.has(k) && pathMeshesByCell.get(k).length > 0) {
      pathSet.add(k);
      heightMap.set(k, 1);
      return;
    }

    // 1. Remove all decor objects at (x, z)
    if (decorByCell.has(k)) {
      const list = decorByCell.get(k);
      list.forEach(obj => {
        if (obj && obj.parent) obj.parent.remove(obj);
      });
      decorByCell.delete(k);
    }

    // 2. Remove all terrain voxels at (x, z)
    if (terrainMeshesByCell.has(k)) {
      const voxList = terrainMeshesByCell.get(k);
      voxList.forEach(mesh => {
        if (mesh && mesh.parent) mesh.parent.remove(mesh);
      });
      terrainMeshesByCell.delete(k);
    }

    // 3. Remove/relocate empty pedestal if sitting on this cell
    const pedIdx = pedestals.findIndex(p => p.x === x && p.z === z);
    if (pedIdx !== -1) {
      const ped = pedestals[pedIdx];
      if (!ped.golem) {
        if (ped.group && ped.group.parent) ped.group.parent.remove(ped.group);
        pedestals.splice(pedIdx, 1);
      }
    }

    // 4. Update heightMap to 1 and add to pathSet
    heightMap.set(k, 1);
    pathSet.add(k);

    // 5. Build cobblestone block and 4 curbs at y = 0.42 (height = 0.85)
    const col = ((Math.abs(x) + Math.abs(z)) % 2 === 0) ? C.COB_L : C.COB_D;
    const parent = targetParent || scene;
    const baseMesh = vox(x, 0.42, z, 0.96, 0.85, 0.96, col, parent);
    const c1 = vox(x, 0.9, z - 0.47, 1.0, 0.18, 0.12, C.COB_CURB, parent);
    const c2 = vox(x, 0.9, z + 0.47, 1.0, 0.18, 0.12, C.COB_CURB, parent);
    const c3 = vox(x - 0.47, 0.9, z, 0.12, 0.18, 1.0, C.COB_CURB, parent);
    const c4 = vox(x + 0.47, 0.9, z, 0.12, 0.18, 1.0, C.COB_CURB, parent);

    registerPathMesh(x, z, baseMesh);
    registerPathMesh(x, z, c1);
    registerPathMesh(x, z, c2);
    registerPathMesh(x, z, c3);
    registerPathMesh(x, z, c4);

    carvedConnectorMeshes.push(baseMesh, c1, c2, c3, c4);

    // 6. Cliff sightline grading: lower foreground terrain if blocking camera
    [[x + 1, z], [x, z + 1], [x + 1, z + 1]].forEach(([nx, nz]) => {
      const nk = `${nx},${nz}`;
      if (!pathSet.has(nk) && (heightMap.get(nk) || 1) > 2) {
        heightMap.set(nk, 2);
        if (terrainMeshesByCell.has(nk)) {
          const meshes = terrainMeshesByCell.get(nk);
          for (let i = meshes.length - 1; i >= 0; i--) {
            if (meshes[i].position.y >= 2.0) {
              if (meshes[i].parent) meshes[i].parent.remove(meshes[i]);
              meshes.splice(i, 1);
            }
          }
        }
      }
    });
  }

  function findConnectorPathOnExistingMap(startOldX, startOldZ, fromCx, fromCz) {
    const startKey = `${startOldX},${startOldZ}`;
    if (pathSet.has(startKey)) {
      return [{ x: startOldX, z: startOldZ }];
    }

    const queue = [{ x: startOldX, z: startOldZ, path: [{ x: startOldX, z: startOldZ }] }];
    const visited = new Set([startKey]);

    const DIRS = [
      { dx: 1, dz: 0 },
      { dx: -1, dz: 0 },
      { dx: 0, dz: 1 },
      { dx: 0, dz: -1 }
    ];

    while (queue.length > 0) {
      const cur = queue.shift();

      if (pathSet.has(`${cur.x},${cur.z}`)) {
        return cur.path;
      }

      if (cur.path.length > 35) continue;

      for (const d of DIRS) {
        const nx = cur.x + d.dx;
        const nz = cur.z + d.dz;
        const nk = `${nx},${nz}`;

        if (visited.has(nk)) continue;

        // Sanctum core avoidance in chunk 0,0
        if (nx <= 3 && nz <= 3 && nx >= 0 && nz >= 0) continue;

        // Occupied golem pedestal avoidance
        const ped = pedestals.find(p => p.x === nx && p.z === nz);
        if (ped && ped.golem) continue;

        // Must stay inside revealed chunks
        const chkX = Math.floor(nx / 16);
        const chkZ = Math.floor(nz / 16);
        if (!ChunkManager.chunks.has(`${chkX},${chkZ}`)) continue;

        visited.add(nk);
        queue.push({
          x: nx,
          z: nz,
          path: [...cur.path, { x: nx, z: nz }]
        });
      }
    }

    return null;
  }

  function generateStartingPathCandidates() {
    const sanctumEntranceX = 4;
    const sanctumEntranceZ = 4;
    const forbiddenSanctum = new Set();
    for (let x = 0; x <= 3; x++) {
      for (let z = 0; z <= 3; z++) {
        forbiddenSanctum.add(`${x},${z}`);
      }
    }

    const candidateConfigs = [
      {
        portalX: 14,
        portalZ: 2,
        chicanes: [{ x: 11, z: 6 }, { x: 8, z: 11 }, { x: 5, z: 8 }]
      },
      {
        portalX: 14,
        portalZ: 5,
        chicanes: [{ x: 10, z: 3 }, { x: 7, z: 7 }, { x: 8, z: 12 }, { x: 5, z: 9 }]
      },
      {
        portalX: 14,
        portalZ: 8,
        chicanes: [{ x: 11, z: 11 }, { x: 7, z: 12 }, { x: 6, z: 6 }]
      },
      {
        portalX: 13,
        portalZ: 1,
        chicanes: [{ x: 13, z: 6 }, { x: 9, z: 9 }, { x: 6, z: 12 }, { x: 4, z: 8 }]
      },
      {
        portalX: 14,
        portalZ: 10,
        chicanes: [{ x: 10, z: 13 }, { x: 8, z: 7 }, { x: 6, z: 9 }]
      },
      {
        portalX: 14,
        portalZ: 12,
        chicanes: [{ x: 9, z: 13 }, { x: 7, z: 9 }, { x: 5, z: 7 }]
      },
      {
        portalX: 12,
        portalZ: 1,
        chicanes: [{ x: 8, z: 2 }, { x: 8, z: 8 }, { x: 6, z: 10 }]
      },
      {
        portalX: 14,
        portalZ: 4,
        chicanes: [{ x: 12, z: 10 }, { x: 8, z: 6 }, { x: 5, z: 10 }]
      }
    ];

    const validCandidates = [];

    candidateConfigs.forEach((cfg, idx) => {
      const path = generateContiguousGridPath(
        cfg.portalX, cfg.portalZ,
        sanctumEntranceX, sanctumEntranceZ,
        1, 14, 1, 14,
        cfg.chicanes,
        forbiddenSanctum
      );

      let touchesForbidden = false;
      path.forEach(pt => {
        if (forbiddenSanctum.has(`${pt[0]},${pt[1]}`)) touchesForbidden = true;
      });
      if (touchesForbidden) return;

      let score = 1000;
      const len = path.length;
      if (len < 22) score -= (22 - len) * 30;
      else if (len > 34) score -= (len - 34) * 20;

      // Count potential pedestal placement slots around path
      let pedestalSlots = 0;
      const pSet = new Set(path.map(p => `${p[0]},${p[1]}`));
      for (let x = 1; x <= 14; x++) {
        for (let z = 1; z <= 14; z++) {
          if (pSet.has(`${x},${z}`)) continue;
          if (forbiddenSanctum.has(`${x},${z}`)) continue;
          let minD = 999;
          path.forEach(pt => {
            const d = Math.abs(pt[0] - x) + Math.abs(pt[1] - z);
            if (d < minD) minD = d;
          });
          if (minD === 1 || minD === 2) pedestalSlots++;
        }
      }
      score += pedestalSlots * 5;

      let turns = 0;
      for (let i = 1; i < path.length - 1; i++) {
        const dx1 = path[i][0] - path[i - 1][0];
        const dz1 = path[i][1] - path[i - 1][1];
        const dx2 = path[i + 1][0] - path[i][0];
        const dz2 = path[i + 1][1] - path[i][1];
        if (dx1 !== dx2 || dz1 !== dz2) turns++;
      }
      score += turns * 20;

      validCandidates.push({
        portalX: cfg.portalX,
        portalZ: cfg.portalZ,
        path: path,
        score: score,
        index: idx
      });
    });

    let bestCandidate = null;
    if (validCandidates.length > 0) {
      validCandidates.sort((a, b) => b.score - a.score);
      // Pick randomly among top 3 to provide procedural variety on restarts!
      const topTier = validCandidates.slice(0, Math.min(3, validCandidates.length));
      bestCandidate = topTier[Math.floor(Math.random() * topTier.length)];
    } else {
      bestCandidate = {
        portalX: 14,
        portalZ: 2,
        path: generateContiguousGridPath(14, 2, 4, 4, 1, 14, 1, 14, [{ x: 11, z: 6 }, { x: 8, z: 11 }, { x: 5, z: 8 }], forbiddenSanctum),
        score: 0,
        index: 0
      };
    }

    console.log(`[StartingMap] Evaluated ${candidateConfigs.length} candidate paths. Selected candidate #${bestCandidate.index} with score ${bestCandidate.score}, length: ${bestCandidate.path.length} tiles.`);
    return bestCandidate;
  }

  function generateExpansionPathCandidates(cx, cz, fromCx, fromCz, dir) {
    const originX = cx * 16;
    const originZ = cz * 16;
    const fromOriginX = fromCx * 16;
    const fromOriginZ = fromCz * 16;

    const parentChunk = ChunkManager.chunks.get(`${fromCx},${fromCz}`);
    const parentPortal = parentChunk ? parentChunk.portalPos : null;

    let candidateConfigs = [];

    if (dir === 'north') {
      const bzNew = originZ + 15;
      const bzOld = fromOriginZ;
      const bxOptions = [originX + 7, originX + 10, originX + 4, originX + 12, originX + 8];
      const portalOptions = [
        { x: originX + 8,  z: originZ + 1 },
        { x: originX + 4,  z: originZ + 2 },
        { x: originX + 12, z: originZ + 1 },
        { x: originX + 6,  z: originZ + 3 },
        { x: originX + 10, z: originZ + 2 }
      ];
      const chicaneOptions = [
        [{ x: originX + 11, z: originZ + 6 }, { x: originX + 5,  z: originZ + 10 }],
        [{ x: originX + 4,  z: originZ + 5 }, { x: originX + 11, z: originZ + 9 }],
        [{ x: originX + 12, z: originZ + 4 }, { x: originX + 7,  z: originZ + 8 }],
        [{ x: originX + 5,  z: originZ + 7 }, { x: originX + 10, z: originZ + 11 }],
        [{ x: originX + 9,  z: originZ + 5 }, { x: originX + 4,  z: originZ + 9 }]
      ];
      if (parentPortal && parentPortal.z <= fromOriginZ + 3) {
        const relX = Math.max(2, Math.min(13, parentPortal.x - fromOriginX));
        const localX = originX + relX;
        const chicX = originX + (((relX + 4) % 10) + 3);
        bxOptions.unshift(localX);
        portalOptions.unshift({ x: localX, z: originZ + 1 });
        chicaneOptions.unshift([{ x: chicX, z: originZ + 6 }, { x: localX, z: originZ + 10 }]);
      }
      for (let i = 0; i < bxOptions.length; i++) {
        candidateConfigs.push({
          borderNew: { x: bxOptions[i], z: bzNew },
          borderOld: { x: bxOptions[i], z: bzOld },
          portal: portalOptions[i],
          chicanes: chicaneOptions[i]
        });
      }
    } else if (dir === 'east') {
      const bxNew = originX;
      const bxOld = fromOriginX + 15;
      const bzOptions = [originZ + 8, originZ + 5, originZ + 11, originZ + 3, originZ + 9];
      const portalOptions = [
        { x: originX + 14, z: originZ + 8 },
        { x: originX + 13, z: originZ + 4 },
        { x: originX + 14, z: originZ + 12 },
        { x: originX + 12, z: originZ + 6 },
        { x: originX + 13, z: originZ + 10 }
      ];
      const chicaneOptions = [
        [{ x: originX + 9,  z: originZ + 4 },  { x: originX + 5, z: originZ + 11 }],
        [{ x: originX + 10, z: originZ + 12 }, { x: originX + 5, z: originZ + 5 }],
        [{ x: originX + 8,  z: originZ + 7 },  { x: originX + 4, z: originZ + 10 }],
        [{ x: originX + 11, z: originZ + 6 },  { x: originX + 6, z: originZ + 9 }],
        [{ x: originX + 8,  z: originZ + 11 }, { x: originX + 4, z: originZ + 6 }]
      ];
      if (parentPortal && parentPortal.x >= fromOriginX + 12) {
        const relZ = Math.max(2, Math.min(13, parentPortal.z - fromOriginZ));
        const localZ = originZ + relZ;
        const chicZ = originZ + (((relZ + 4) % 10) + 3);
        bzOptions.unshift(localZ);
        portalOptions.unshift({ x: originX + 14, z: localZ });
        chicaneOptions.unshift([{ x: originX + 9, z: chicZ }, { x: originX + 5, z: localZ }]);
      }
      for (let i = 0; i < bzOptions.length; i++) {
        candidateConfigs.push({
          borderNew: { x: bxNew, z: bzOptions[i] },
          borderOld: { x: bxOld, z: bzOptions[i] },
          portal: portalOptions[i],
          chicanes: chicaneOptions[i]
        });
      }
    } else if (dir === 'south') {
      const bzNew = originZ;
      const bzOld = fromOriginZ + 15;
      const bxOptions = [originX + 8, originX + 11, originX + 5, originX + 12, originX + 7];
      const portalOptions = [
        { x: originX + 8,  z: originZ + 14 },
        { x: originX + 12, z: originZ + 13 },
        { x: originX + 4,  z: originZ + 14 },
        { x: originX + 10, z: originZ + 12 },
        { x: originX + 6,  z: originZ + 13 }
      ];
      const chicaneOptions = [
        [{ x: originX + 5,  z: originZ + 9 }, { x: originX + 11, z: originZ + 5 }],
        [{ x: originX + 11, z: originZ + 10}, { x: originX + 4,  z: originZ + 6 }],
        [{ x: originX + 7,  z: originZ + 8 }, { x: originX + 11, z: originZ + 4 }],
        [{ x: originX + 4,  z: originZ + 11}, { x: originX + 10, z: originZ + 7 }],
        [{ x: originX + 9,  z: originZ + 9 }, { x: originX + 5,  z: originZ + 5 }]
      ];
      if (parentPortal && parentPortal.z >= fromOriginZ + 12) {
        const relX = Math.max(2, Math.min(13, parentPortal.x - fromOriginX));
        const localX = originX + relX;
        const chicX = originX + (((relX + 4) % 10) + 3);
        bxOptions.unshift(localX);
        portalOptions.unshift({ x: localX, z: originZ + 14 });
        chicaneOptions.unshift([{ x: chicX, z: originZ + 9 }, { x: localX, z: originZ + 5 }]);
      }
      for (let i = 0; i < bxOptions.length; i++) {
        candidateConfigs.push({
          borderNew: { x: bxOptions[i], z: bzNew },
          borderOld: { x: bxOptions[i], z: bzOld },
          portal: portalOptions[i],
          chicanes: chicaneOptions[i]
        });
      }
    } else {
      const bxNew = originX + 15;
      const bxOld = fromOriginX;
      const bzOptions = [originZ + 8, originZ + 5, originZ + 11, originZ + 4, originZ + 10];
      const portalOptions = [
        { x: originX + 1, z: originZ + 8 },
        { x: originX + 2, z: originZ + 4 },
        { x: originX + 1, z: originZ + 12 },
        { x: originX + 3, z: originZ + 6 },
        { x: originX + 2, z: originZ + 10 }
      ];
      const chicaneOptions = [
        [{ x: originX + 6, z: originZ + 4 },  { x: originX + 10, z: originZ + 11 }],
        [{ x: originX + 5, z: originZ + 11 }, { x: originX + 11, z: originZ + 5 }],
        [{ x: originX + 7, z: originZ + 8 },  { x: originX + 11, z: originZ + 11 }],
        [{ x: originX + 4, z: originZ + 6 },  { x: originX + 10, z: originZ + 9 }],
        [{ x: originX + 7, z: originZ + 10 }, { x: originX + 11, z: originZ + 6 }]
      ];
      if (parentPortal && parentPortal.x <= fromOriginX + 3) {
        const relZ = Math.max(2, Math.min(13, parentPortal.z - fromOriginZ));
        const localZ = originZ + relZ;
        const chicZ = originZ + (((relZ + 4) % 10) + 3);
        bzOptions.unshift(localZ);
        portalOptions.unshift({ x: originX + 1, z: localZ });
        chicaneOptions.unshift([{ x: originX + 6, z: chicZ }, { x: originX + 10, z: localZ }]);
      }
      for (let i = 0; i < bzOptions.length; i++) {
        candidateConfigs.push({
          borderNew: { x: bxNew, z: bzOptions[i] },
          borderOld: { x: bxOld, z: bzOptions[i] },
          portal: portalOptions[i],
          chicanes: chicaneOptions[i]
        });
      }
    }

    let bestCandidate = null;
    let bestScore = -Infinity;

    candidateConfigs.forEach((cfg, idx) => {
      const newChunkPath = generateContiguousGridPath(
        cfg.portal.x, cfg.portal.z,
        cfg.borderNew.x, cfg.borderNew.z,
        originX, originX + 15, originZ, originZ + 15,
        cfg.chicanes
      );

      const connectorOldPath = findConnectorPathOnExistingMap(
        cfg.borderOld.x, cfg.borderOld.z,
        fromCx, fromCz
      );

      if (!connectorOldPath || connectorOldPath.length === 0) return;

      let score = 1000;
      const connLen = connectorOldPath.length;
      if (connLen <= 2) score += 250; // direct alignment with old road/portal!
      else if (connLen <= 8) score += 120;
      else score -= (connLen - 8) * 20;

      const chunkLen = newChunkPath.length;
      if (chunkLen < 18) score -= (18 - chunkLen) * 30;
      else if (chunkLen > 34) score -= (chunkLen - 34) * 20;

      let turns = 0;
      for (let i = 1; i < newChunkPath.length - 1; i++) {
        const dx1 = newChunkPath[i][0] - newChunkPath[i - 1][0];
        const dz1 = newChunkPath[i][1] - newChunkPath[i - 1][1];
        const dx2 = newChunkPath[i + 1][0] - newChunkPath[i][0];
        const dz2 = newChunkPath[i + 1][1] - newChunkPath[i][1];
        if (dx1 !== dx2 || dz1 !== dz2) turns++;
      }
      score += turns * 25;

      if (score > bestScore) {
        bestScore = score;
        bestCandidate = {
          portal: cfg.portal,
          borderNew: cfg.borderNew,
          borderOld: cfg.borderOld,
          newChunkPath: newChunkPath,
          connectorOldTiles: connectorOldPath,
          chicanes: cfg.chicanes,
          score: score,
          index: idx
        };
      }
    });

    if (!bestCandidate) {
      console.error(`Failed to find viable candidate for [${cx},${cz}]. Using fallback.`);
      const fallback = candidateConfigs[0];
      const newChunkPath = generateContiguousGridPath(
        fallback.portal.x, fallback.portal.z,
        fallback.borderNew.x, fallback.borderNew.z,
        originX, originX + 15, originZ, originZ + 15,
        fallback.chicanes
      );
      const conn = findConnectorPathOnExistingMap(fallback.borderOld.x, fallback.borderOld.z, fromCx, fromCz) || [fallback.borderOld];
      bestCandidate = {
        portal: fallback.portal,
        borderNew: fallback.borderNew,
        borderOld: fallback.borderOld,
        newChunkPath: newChunkPath,
        connectorOldTiles: conn,
        chicanes: fallback.chicanes,
        score: 0,
        index: 0
      };
    }

    console.log(`[ChunkManager] Evaluated 5 expansion path candidates for [${cx},${cz}]. Selected candidate #${bestCandidate.index} with score ${bestCandidate.score}. Chunk path: ${bestCandidate.newChunkPath.length} tiles, carved connector: ${bestCandidate.connectorOldTiles.length} tiles.`);
    return bestCandidate;
  }

  function destroyCurrentLevel() {
    // 1. Remove all island root objects from scene
    islandRootObjects.forEach(obj => {
      if (obj && obj.parent) obj.parent.remove(obj);
    });
    islandRootObjects = [];

    // 2. Remove all pedestals from scene
    pedestals.forEach(ped => {
      if (ped && ped.group && ped.group.parent) ped.group.parent.remove(ped.group);
    });
    pedestals = [];
    PEDESTAL_CONFIGS = [];

    // 3. Remove all expansion chunks from scene
    ChunkManager.chunks.forEach(chunk => {
      if (chunk.group && chunk.group.parent) chunk.group.parent.remove(chunk.group);
    });
    ChunkManager.chunks.clear();
    ChunkManager.activePortals = [];
    ChunkManager.animatingVoxels = [];
    ChunkManager.clear3DArrows();
    ChunkManager.clear3DBanners();
    ChunkManager.nextPedestalId = 10;
    GameState.awaitingExpansion = false;
    document.getElementById('expansion-prompt-bar')?.classList.add('hidden');

    // 4. Remove all carved connector meshes
    carvedConnectorMeshes.forEach(mesh => {
      if (mesh && mesh.parent) mesh.parent.remove(mesh);
    });
    carvedConnectorMeshes = [];

    // Clear active tornadoes
    for (let i = activeTornadoes.length - 1; i >= 0; i--) {
      const t = activeTornadoes[i];
      if (t.mesh && t.mesh.parent) t.mesh.parent.remove(t.mesh);
    }
    activeTornadoes = [];

    // 5. Clear all registries and maps
    terrainMeshesByCell.clear();
    decorByCell.clear();
    pathMeshesByCell.clear();
    heightMap.clear();
    pathSet.clear();
    sanctumEyes = [];
    waterfallFlow = [];
    waterfallFoam = [];
    oasisWater = [];
    environmentalProps = [];
    portalRunes = [];
    startingPortalGroup = null;
    activeRoughPatches = [];
    ditherTextureCache.forEach(tex => tex.dispose());
    ditherTextureCache.clear();
  }

  function buildProceduralStartingIsland() {
    islandRootObjects = [];
    activeRoughPatches = [];
    generateRoughPatchesForChunk(0, 0);

    // 1. Bedrock Plinth & Shadow Plane
    const plinthGroup = new THREE.Group();
    for (let x = 0; x < 16; x++) {
      for (let z = 0; z < 16; z++) {
        vox(x, -0.5, z, 1, 1, 1, C.SAND_X, plinthGroup);
        vox(x, -1.5, z, 1, 1, 1, C.BED_1,  plinthGroup);
        vox(x, -2.5, z, 1, 1, 1, C.BED_2,  plinthGroup);
        vox(x, -3.5, z, 1, 1, 1, C.BED_3,  plinthGroup);
      }
    }
    const shadowPlane = new THREE.Mesh(
      new THREE.PlaneGeometry(50, 50),
      new THREE.ShadowMaterial({ opacity: 0.45 })
    );
    shadowPlane.rotation.x = -Math.PI / 2;
    shadowPlane.position.set(7.5, -4.01, 7.5);
    shadowPlane.receiveShadow = true;
    scene.add(shadowPlane);
    scene.add(plinthGroup);
    islandRootObjects.push(shadowPlane, plinthGroup);

    // 2. Pre-calculate Multiple Path Candidates & Select Optimal Contiguous Path
    const winner = generateStartingPathCandidates();
    PATH_TILES = winner.path;
    pathSet = new Set(PATH_TILES.map(p => `${p[0]},${p[1]}`));
    const portalX = winner.portalX;
    const portalZ = winner.portalZ;

    // 3. Base Heightmap with smart visibility slope:
    // Path cells are carved to height 1. Higher elevation in North-West (mesa backdrop), lowlands in South-East.
    for (let x = 0; x < 16; x++) {
      for (let z = 0; z < 16; z++) {
        if (pathSet.has(`${x},${z}`)) {
          heightMap.set(`${x},${z}`, 1);
          continue;
        }
        let h = 1;
        if (x <= 5 && z <= 5) {
          h = 3;
          if (x <= 2 && z <= 2) h = 4;
        } else if (x <= 7 && z <= 7) {
          h = 2;
        }
        heightMap.set(`${x},${z}`, h);
      }
    }

    // 4. Ancient Sanctum placed at (2.5, 1.0, 2.5) looking directly into the player's isometric camera!
    const sanctumGrp = buildSanctum(2.5, 1.0, 2.5, Math.PI * 0.25);
    if (sanctumGrp) islandRootObjects.push(sanctumGrp);

    // 5. Build Cobblestone Path Meshes & register in pathMeshesByCell
    const pathGroup = new THREE.Group();
    PATH_TILES.forEach((pt, idx) => {
      const col = (idx % 2 === 0) ? C.COB_L : C.COB_D;
      const px = pt[0], pz = pt[1];
      const m1 = vox(px, 0.42, pz, 0.96, 0.85, 0.96, col, pathGroup);
      const m2 = vox(px, 0.9, pz - 0.47, 1.0, 0.18, 0.12, C.COB_CURB, pathGroup);
      const m3 = vox(px, 0.9, pz + 0.47, 1.0, 0.18, 0.12, C.COB_CURB, pathGroup);
      const m4 = vox(px - 0.47, 0.9, pz, 0.12, 0.18, 1.0, C.COB_CURB, pathGroup);
      const m5 = vox(px + 0.47, 0.9, pz, 0.12, 0.18, 1.0, C.COB_CURB, pathGroup);
      registerPathMesh(px, pz, m1);
      registerPathMesh(px, pz, m2);
      registerPathMesh(px, pz, m3);
      registerPathMesh(px, pz, m4);
      registerPathMesh(px, pz, m5);
    });

    // Build Alien Spawn Portal at (portalX, portalZ)
    const portalGroup = buildPortalMesh(portalX, 0.85, portalZ);
    startingPortalGroup = portalGroup;
    pathGroup.add(portalGroup);
    scene.add(pathGroup);
    islandRootObjects.push(pathGroup);

    // 6. Compute Smooth Waypoints
    WAYPOINTS = PATH_TILES.map(pt => new THREE.Vector3(pt[0], 0.85, pt[1]));

    // 7. Place 10 Rune-Carved Pedestals with Unobstructed Sightlines & Glowing Beacons!
    const pedPositions = [];
    const usedPedKeys = new Set();
    const tryAddPed = (px, pz) => {
      if (pedPositions.length >= 10) return;
      if (px < 1 || px > 14 || pz < 1 || pz > 14) return;
      const k = `${px},${pz}`;
      if (pathSet.has(k) || usedPedKeys.has(k)) return;
      if (px <= 3 && pz <= 3) return; // Sanctum core avoidance
      usedPedKeys.add(k);
      pedPositions.push({ x: px, z: pz });
    };

    const designerOffsets = [
      { x: 13, z: 4 }, { x: 12, z: 1 }, { x: 12, z: 8 }, { x: 10, z: 5 },
      { x: 9,  z: 9 }, { x: 9,  z: 13 }, { x: 7,  z: 13 }, { x: 6,  z: 10 },
      { x: 6,  z: 6 }, { x: 3,  z: 6 },  { x: 2,  z: 8 },  { x: 8,  z: 3 },
      { x: 11, z: 3 }, { x: 8,  z: 5 },  { x: 5,  z: 12 }, { x: 13, z: 9 }
    ];
    designerOffsets.forEach(cand => tryAddPed(cand.x, cand.z));

    if (pedPositions.length < 10) {
      for (let i = 0; i < PATH_TILES.length; i++) {
        const [px, pz] = PATH_TILES[i];
        [
          [px + 1, pz], [px - 1, pz], [px, pz + 1], [px, pz - 1],
          [px + 1, pz + 1], [px - 1, pz - 1], [px + 2, pz], [px, pz + 2]
        ].forEach(([cx, cz]) => tryAddPed(cx, cz));
        if (pedPositions.length >= 10) break;
      }
    }

    PEDESTAL_CONFIGS = [];
    let pedId = 0;
    pedPositions.forEach(pos => {
      // Sightline clearance: Ensure foreground cells (px+1, pz), (px, pz+1), (px+1, pz+1) do not occlude!
      const fg1 = `${pos.x + 1},${pos.z}`;
      const fg2 = `${pos.x},${pos.z + 1}`;
      const fg3 = `${pos.x + 1},${pos.z + 1}`;
      if ((heightMap.get(fg1) || 1) > 1) heightMap.set(fg1, 1);
      if ((heightMap.get(fg2) || 1) > 1) heightMap.set(fg2, 1);
      if ((heightMap.get(fg3) || 1) > 1) heightMap.set(fg3, 1);

      const h = heightMap.get(`${pos.x},${pos.z}`) || 1;
      const ped = createPedestalMesh(pedId, pos.x, h, pos.z);
      pedestals.push(ped);
      scene.add(ped.group);
      PEDESTAL_CONFIGS.push({ id: pedId, x: pos.x, z: pos.z, y: h });
      pedId++;
    });

    // 8. Render Terrain Meshes based on heightMap & register in terrainMeshesByCell
    const terrainGroup = new THREE.Group();
    createSandRoughnessTextures();
    for (let x = 0; x < 16; x++) {
      for (let z = 0; z < 16; z++) {
        if (pathSet.has(`${x},${z}`)) continue;
        const maxH = heightMap.get(`${x},${z}`) || 1;
        for (let y = 1; y <= maxH; y++) {
          const isTop = (y === maxH);
          let tileMap = null;
          if (isTop) {
            tileMap = getSandDitherTexture(x, z);
          }
          const col = getTerrainColor(y, maxH, x, z, !!tileMap);
          const m = vox(x, y - 0.5, z, 1, 1, 1, col, terrainGroup, 0, 0, 1, tileMap);
          registerTerrainVoxel(x, z, m);
        }
      }
    }

    scene.add(terrainGroup);
    islandRootObjects.push(terrainGroup);

    // 9. Procedural Wind Particles & Airborne Dust Streaks
    WindManager.init(scene);
    if (WindManager.group) islandRootObjects.push(WindManager.group);

    // 10. Optional Procedural Waterfall and Plunge Pool beside Sanctum mesa (~35% chance)
    const shouldSpawnWaterfall = Math.random() < 0.35;
    if (shouldSpawnWaterfall) {
      const watGrp = buildWaterfallAndOasis(scene, 1.0, 4.0);
      if (watGrp) islandRootObjects.push(watGrp);
    }

    // 11. Populate with Procedural Terrain Assets (Flora, Ruins, Rocks, and rare Oasis)
    const decors = buildProceduralDecorations(scene, 0, 0);
    if (decors && decors.length) {
      islandRootObjects.push(...decors);
    }

    // 12. Procedural Overworld Pebbles (Clustered gravel beds, scattered stones, clean sand zones)
    const pebbleGrp = populateChunkPebbles(scene, 0, 0);
    if (pebbleGrp) islandRootObjects.push(pebbleGrp);

    // 12. Create range ring meshes (if not yet created)
    if (!rangeRingMesh) {
      const ringGeo = new THREE.RingGeometry(0.1, 1.0, 36);
      const ringMat = new THREE.MeshBasicMaterial({
        color: 0x39FF14,
        transparent: true,
        opacity: 0.35,
        side: THREE.DoubleSide,
        depthWrite: false
      });
      rangeRingMesh = new THREE.Mesh(ringGeo, ringMat);
      rangeRingMesh.rotation.x = -Math.PI / 2;
      rangeRingMesh.visible = false;
      scene.add(rangeRingMesh);

      const prevMat = new THREE.MeshBasicMaterial({
        color: 0xFFD25A,
        transparent: true,
        opacity: 0.25,
        side: THREE.DoubleSide,
        depthWrite: false
      });
      rangeRingPreviewMesh = new THREE.Mesh(ringGeo.clone(), prevMat);
      rangeRingPreviewMesh.rotation.x = -Math.PI / 2;
      rangeRingPreviewMesh.visible = false;
      scene.add(rangeRingPreviewMesh);
    }
  }

  function showRangeRing(pos, radius, colorHex) {
    if (!rangeRingMesh) return;
    rangeRingMesh.position.set(pos.x, pos.y + 0.05, pos.z);
    rangeRingMesh.scale.set(radius, radius, 1);
    rangeRingMesh.material.color.setHex(colorHex || 0x39FF14);
    rangeRingMesh.visible = true;
  }

  function hideRangeRing() {
    if (rangeRingMesh) rangeRingMesh.visible = false;
  }

  function showPreviewRangeRing(pos, radius, colorHex) {
    if (!rangeRingPreviewMesh) return;
    rangeRingPreviewMesh.position.set(pos.x, pos.y + 0.04, pos.z);
    rangeRingPreviewMesh.scale.set(radius, radius, 1);
    rangeRingPreviewMesh.material.color.setHex(colorHex || 0xFFD25A);
    rangeRingPreviewMesh.visible = true;
  }

  function hidePreviewRangeRing() {
    if (rangeRingPreviewMesh) rangeRingPreviewMesh.visible = false;
  }

  function updateRangeRingPreview() {
    if (hoveredPedestal && !hoveredPedestal.golem) {
      const cfg = GOLEM_CONFIGS[GameState.selectedGolemType];
      if (cfg) {
        showPreviewRangeRing(hoveredPedestal.group.position, cfg.range, cfg.color);
      }
    } else {
      hidePreviewRangeRing();
    }
  }

  // ========================================================
  // PROCEDURAL GOLEM FACTORIES (Phase 1 Refined)
  // ========================================================
  const GS = 0.16;

  function createStoneGolemModel() {
    const g = new THREE.Group();
    vox(-1.7, 0.6, 0, 2.0, 1.2, 2.4, C.SG_DK, g);
    vox( 1.7, 0.6, 0, 2.0, 1.2, 2.4, C.SG_DK, g);
    vox(-1.7, 2.5, 0, 1.8, 2.6, 2.0, C.SG_D, g);
    vox( 1.7, 2.5, 0, 1.8, 2.6, 2.0, C.SG_D, g);
    vox(-1.7, 2.6, 1.0, 1.4, 1.0, 0.4, C.SG_M, g);
    vox( 1.7, 2.6, 1.0, 1.4, 1.0, 0.4, C.SG_M, g);

    const upper = new THREE.Group();
    vox(0, 5.6, 0, 5.6, 4.0, 3.4, C.SG_M, upper);
    vox(0, 5.8, 1.6, 3.6, 2.4, 0.5, C.SG_D, upper);
    vox(0, 5.4, 1.8, 2.0, 1.4, 0.3, C.SG_L, upper);
    vox(-3.8, 6.8, 0, 2.8, 2.4, 3.2, C.SG_M, upper);
    vox( 3.8, 6.8, 0, 2.8, 2.4, 3.2, C.SG_M, upper);
    vox(-3.8, 8.1, 0, 3.0, 0.4, 3.4, C.MOSS, upper);
    vox( 3.8, 8.1, 0, 3.0, 0.4, 3.4, C.MOSS, upper);
    vox(-3.6, 8.5,  0.5, 0.35, 0.35, 0.35, C.FLOWER_Y, upper, C.FLOWER_Y, 0.7);
    vox( 3.7, 8.5, -0.4, 0.35, 0.35, 0.35, C.FLOWER_Y, upper, C.FLOWER_Y, 0.7);

    vox(-3.8, 3.8, 0, 1.9, 4.0, 2.2, C.SG_D, upper);
    vox( 3.8, 3.8, 0, 1.9, 4.0, 2.2, C.SG_D, upper);
    vox(-3.8, 1.4, 0.3, 2.4, 2.2, 2.6, C.SG_DK, upper);
    vox( 3.8, 1.4, 0.3, 2.4, 2.2, 2.6, C.SG_DK, upper);

    vox(0, 7.8, 0, 2.0, 0.8, 2.0, C.SG_DK, upper);
    vox(0, 9.6, 0.2, 4.0, 3.2, 3.4, C.SG_L, upper);
    vox(0, 10.6, 1.7, 4.2, 0.6, 0.6, C.SG_M, upper);
    vox(0, 9.4, 1.7, 2.8, 2.0, 0.4, C.SG_DK, upper);
    vox(0, 9.5, 1.95, 1.8, 0.3, 0.15, C.SG_L, upper);
    vox(-0.7, 9.9, 1.95, 0.5, 0.4, 0.1, 0x1A1A1A, upper);
    vox( 0.7, 9.9, 1.95, 0.5, 0.4, 0.1, 0x1A1A1A, upper);

    g.add(upper);
    g.scale.setScalar(GS);
    g.userData.upper = upper;
    return g;
  }

  function createOakGolemModel() {
    const g = new THREE.Group();
    vox(-1.6, 0.6, 0, 1.9, 1.2, 2.2, C.OG_WD_DK, g);
    vox( 1.6, 0.6, 0, 1.9, 1.2, 2.2, C.OG_WD_DK, g);
    vox(-1.6, 2.5, 0, 1.7, 2.6, 1.9, C.OG_WD, g);
    vox( 1.6, 2.5, 0, 1.7, 2.6, 1.9, C.OG_WD, g);

    const upper = new THREE.Group();
    vox(0, 5.5, 0, 5.2, 4.2, 3.2, C.OG_TAN, upper);
    vox(0, 5.5, 1.5, 3.6, 3.6, 0.4, C.OG_WD, upper);
    vox(-3.6, 6.8, 0, 2.6, 2.2, 2.8, C.OG_TAN, upper);
    vox( 3.6, 6.8, 0, 2.6, 2.2, 2.8, C.OG_TAN, upper);
    vox(-3.6, 3.8, 0, 1.8, 3.8, 2.0, C.OG_WD, upper);
    vox( 3.6, 3.8, 0, 1.8, 3.8, 2.0, C.OG_WD, upper);
    vox(-3.6, 1.5, 0.3, 2.1, 2.0, 2.3, C.OG_WD_DK, upper);
    vox( 3.6, 1.5, 0.3, 2.1, 2.0, 2.3, C.OG_WD_DK, upper);

    vox(0, 9.4, 0, 3.8, 3.0, 3.2, C.OG_TAN, upper);
    vox(0, 10.6, 1.2, 4.0, 0.5, 0.8, C.OG_WD, upper);

    // Barrel
    vox(0, 9.4, 1.8, 2.2, 2.2, 0.6, C.OG_WD_DK, upper);
    vox(0, 9.4, 2.6, 1.4, 1.4, 1.6, C.OG_WD, upper);
    vox(0, 9.4, 2.2, 1.6, 1.6, 0.3, C.OG_MTL, upper);
    vox(0, 9.4, 3.2, 1.5, 1.5, 0.3, C.OG_MTL, upper);
    vox(0, 9.4, 3.6, 1.3, 1.3, 0.3, C.OG_WD_DK, upper);
    vox(0, 9.4, 3.8, 0.8, 0.8, 0.15, 0x151210, upper);

    g.add(upper);
    g.scale.setScalar(GS);
    g.userData.upper = upper;
    return g;
  }

  function createBrickGolemModel() {
    const g = new THREE.Group();
    vox(-1.8, 0.6, 0, 2.3, 1.2, 2.7, C.BG_BR_DK, g);
    vox( 1.8, 0.6, 0, 2.3, 1.2, 2.7, C.BG_BR_DK, g);
    vox(-1.8, 2.8, 0, 2.1, 3.2, 2.4, C.BG_BR, g);
    vox( 1.8, 2.8, 0, 2.1, 3.2, 2.4, C.BG_BR, g);

    const upper = new THREE.Group();
    vox(0, 6.4, 0, 6.2, 4.8, 3.8, C.BG_BR, upper);
    vox(-2.9, 6.4, 1.5, 0.6, 4.6, 0.6, C.BG_SL, upper);
    vox( 2.9, 6.4, 1.5, 0.6, 4.6, 0.6, C.BG_SL, upper);
    vox(0, 8.8, 1.5, 5.8, 0.5, 0.7, C.BG_SL, upper);

    // Glowing chest rune
    vox(0, 6.2, 1.8, 2.8, 3.2, 0.5, 0x121414, upper);
    vox(0, 6.3, 2.05, 0.45, 2.2, 0.15, C.GLOW_GRN, upper, C.GLOW_GRN, 1.8);
    vox(0, 6.7, 2.05, 1.8,  0.4, 0.15, C.GLOW_GRN, upper, C.GLOW_GRN, 1.8);

    // Arms
    const armL = new THREE.Group();
    vox(-4.2, 7.4, 0, 3.0, 2.6, 3.4, C.BG_BR, armL);
    vox(-4.2, 4.0, 0, 2.2, 4.4, 2.4, C.BG_BR_DK, armL);
    vox(-4.2, 1.2, 0.4, 2.6, 2.4, 2.8, C.BG_SL_DK, armL);
    upper.add(armL);

    const armR = new THREE.Group();
    vox( 4.2, 7.4, 0, 3.0, 2.6, 3.4, C.BG_BR, armR);
    vox( 4.2, 4.0, 0, 2.2, 4.4, 2.4, C.BG_BR_DK, armR);
    vox( 4.2, 1.2, 0.4, 2.6, 2.4, 2.8, C.BG_SL_DK, armR);
    upper.add(armR);

    vox(0, 9.6, -0.2, 3.0, 2.2, 2.8, C.BG_BR, upper);
    vox(-0.6, 9.9, 1.1, 0.5, 0.35, 0.2, 0xFF3300, upper, 0xFF3300, 1.0);
    vox( 0.6, 9.9, 1.1, 0.5, 0.35, 0.2, 0xFF3300, upper, 0xFF3300, 1.0);

    g.add(upper);
    g.scale.setScalar(GS);
    g.userData.upper = upper;
    g.userData.armL = armL;
    g.userData.armR = armR;
    return g;
  }

  function createDioriteGolemModel() {
    const g = new THREE.Group();
    vox(-1.5, 0.5, 0, 1.8, 1.0, 2.2, C.DG_G, g);
    vox( 1.5, 0.5, 0, 1.8, 1.0, 2.2, C.DG_G, g);
    vox(-1.5, 2.3, 0, 1.5, 2.6, 1.8, C.DG_W, g);
    vox( 1.5, 2.3, 0, 1.5, 2.6, 1.8, C.DG_W, g);

    const upper = new THREE.Group();
    vox(0, 6.0, -1.0, 5.2, 4.6, 1.2, C.DG_W, upper);
    vox(-2.3, 6.0, 0, 0.8, 4.6, 3.2, C.DG_W, upper);
    vox( 2.3, 6.0, 0, 0.8, 4.6, 3.2, C.DG_W, upper);
    vox(0, 8.2, 0, 5.2, 0.4, 3.2, C.DG_W, upper);
    vox(0, 3.8, 0, 5.2, 0.4, 3.2, C.DG_G, upper);
    vox(0, 8.2, 1.5, 5.4, 0.25, 0.25, C.DG_GLD, upper, C.DG_GLD, 0.4);

    // Floating crystal core
    const core = new THREE.Group();
    core.position.set(0, 6.0, 0.2);
    const cr1 = vox(0, 0, 0, 1.1, 1.7, 1.1, C.DG_GLD, core, C.DG_GLD, 1.8);
    cr1.rotation.y = Math.PI / 4;
    const cr2 = vox(0, 0, 0, 1.5, 0.9, 1.5, C.DG_GDK_G, core, C.DG_GLD, 1.4);
    cr2.rotation.y = Math.PI / 4;
    vox(0, 0, 0, 0.6, 0.6, 0.6, 0xFFFFFF, core, 0xFFFFFF, 2.0);
    upper.add(core);

    vox(-3.7, 7.2, 0, 2.4, 2.0, 2.6, C.DG_W, upper);
    vox( 3.7, 7.2, 0, 2.4, 2.0, 2.6, C.DG_W, upper);
    vox(-3.7, 4.2, 0, 1.6, 4.0, 1.8, C.DG_G, upper);
    vox( 3.7, 4.2, 0, 1.6, 4.0, 1.8, C.DG_G, upper);
    vox(-3.7, 1.6, 0.2, 1.9, 1.8, 2.1, C.DG_W, upper);
    vox( 3.7, 1.6, 0.2, 1.9, 1.8, 2.1, C.DG_W, upper);

    vox(0, 10.0, 0, 3.4, 2.8, 3.0, C.DG_W, upper);
    vox(0, 10.9, 1.2, 3.6, 0.4, 0.4, C.DG_GLD, upper, C.DG_GLD, 0.7);
    vox(0, 10.2, 1.45, 2.4, 0.35, 0.2, C.DG_GLD, upper, C.DG_GLD, 1.6);

    g.add(upper);
    g.scale.setScalar(GS);
    g.userData.upper = upper;
    g.userData.core = core;
    return g;
  }

  // ========================================================
  // GOLEM INSTANCE CLASS (Phase 3 Forward-Compatible)
  // ========================================================
  class GolemInstance {
    constructor(type, pedestal) {
      this.type = type;
      this.config = GOLEM_CONFIGS[type];
      this.pedestal = pedestal;

      this.level = 1;
      this.totalInvested = this.config.cost;
      this.damage = this.config.damage;
      this.range = this.config.range;
      this.cooldown = this.config.cooldown;
      this.cooldownTimer = 0.2; // slight ready delay
      this.targetingMode = 'first'; // 'first' | 'last' | 'strongest' | 'closest'

      this.currentTarget = null;
      this.attackAnimTimer = 0;
      this.baseRotY = Math.PI * 0.25;

      // Elemental Infusion (Thunder, Earth, Fire, Water)
      this.element = null;
      this.elementMesh = null;

      // Instantiate 3D model
      if (type === 'stone') this.model = createStoneGolemModel();
      else if (type === 'oak') this.model = createOakGolemModel();
      else if (type === 'brick') this.model = createBrickGolemModel();
      else if (type === 'diorite') this.model = createDioriteGolemModel();

      this.position = new THREE.Vector3(pedestal.x, pedestal.y + 0.67, pedestal.z);
      this.model.position.copy(this.position);
      this.model.rotation.y = this.baseRotY;
      scene.add(this.model);

      pedestal.golem = this;
      activeGolems.push(this);

      // Spawn stone dust puff
      CombatManager.spawnParticleBurst(this.position, 8, C.PED_BASE);
      GameState.playSound('golemPlace');
    }

    update(dt) {
      // Cooldown timer
      if (this.cooldownTimer > 0) {
        this.cooldownTimer -= dt;
      }

      // Idle breathing
      const t = clock.getElapsedTime();
      this.model.position.y = this.position.y + Math.sin(t * 1.8 + this.pedestal.id) * 0.04;

      // Diorite core spin
      if (this.model.userData.core) {
        this.model.userData.core.rotation.y += 2.5 * dt;
      }

      // Attack recoil / slam animation
      if (this.attackAnimTimer > 0) {
        this.attackAnimTimer -= dt;
        if (this.type === 'brick' && this.model.userData.armL) {
          const armRot = Math.sin((this.attackAnimTimer / 0.3) * Math.PI) * 0.8;
          this.model.userData.armL.rotation.x = -armRot;
          this.model.userData.armR.rotation.x = -armRot;
        }
      }

      // Tier 3 Animations
      if (this.model.userData.halo) {
        this.model.userData.halo.rotation.y += 2.0 * dt;
        this.model.userData.halo.position.y = 1.9 + Math.sin(t * 3.0) * 0.04;
      }
      if (this.model.userData.stoneCrags) {
        this.model.userData.stoneCrags.position.y = Math.sin(t * 2.5) * 0.05;
      }
      if (this.model.userData.astrolabeOuter && this.model.userData.astrolabeInner) {
        this.model.userData.astrolabeOuter.rotation.y += 2.4 * dt;
        this.model.userData.astrolabeOuter.rotation.x += 1.2 * dt;
        this.model.userData.astrolabeInner.rotation.y -= 3.0 * dt;
        this.model.userData.astrolabeInner.rotation.z += 1.8 * dt;
      }

      // Tier 4 Vanguard Animations
      if (this.model.userData.lvl4Vanguard) {
        if (this.model.userData.lvl4Vanguard.userData.crystals) {
          this.model.userData.lvl4Vanguard.userData.crystals.rotation.y += 2.6 * dt;
        }
        if (this.model.userData.prismPylons) {
          this.model.userData.prismPylons.position.y = Math.sin(t * 3.0) * 0.06;
          this.model.userData.prismPylons.rotation.y += 1.5 * dt;
        }
      }

      // Tier 5 Ascended Titan crown, motes & aura rotations
      if (this.model.userData.ascended) {
        if (this.model.userData.ascCrownOuter) this.model.userData.ascCrownOuter.rotation.y -= 1.6 * dt;
        if (this.model.userData.ascCrownInner) this.model.userData.ascCrownInner.rotation.y += 2.2 * dt;
        if (this.model.userData.ascMotes) {
          this.model.userData.ascMotes.rotation.y += 3.0 * dt;
          this.model.userData.ascMotes.position.y = 1.0 + Math.sin(t * 4.0) * 0.06;
        }
        if (this.model.userData.ascOrbitAsteroids) {
          this.model.userData.ascOrbitAsteroids.rotation.y += 2.2 * dt;
          this.model.userData.ascOrbitAsteroids.children.forEach((c, idx) => {
            c.rotation.x += (1.0 + idx * 0.5) * dt;
            c.rotation.z += (0.8 + idx * 0.4) * dt;
          });
        }
        if (this.model.userData.ascOrbitWisps) {
          this.model.userData.ascOrbitWisps.rotation.y += 2.8 * dt;
          this.model.userData.ascOrbitWisps.position.y = 1.1 + Math.sin(t * 3.5) * 0.08;
        }
        if (this.model.userData.ascOrbitCinders) {
          this.model.userData.ascOrbitCinders.rotation.y += 4.0 * dt;
          this.model.userData.ascOrbitCinders.position.y = 0.9 + Math.sin(t * 5.0) * 0.05;
        }
        if (this.model.userData.ascOrbitStars) {
          this.model.userData.ascOrbitStars.rotation.y -= 2.5 * dt;
          this.model.userData.ascOrbitStars.children.forEach(c => { c.rotation.y += 4.0 * dt; });
        }
        if (this.model.userData.ascSolarMandala) {
          this.model.userData.ascSolarMandala.rotation.z += 0.8 * dt;
        }
        if (this.model.userData.ascAura) this.model.userData.ascAura.rotation.z += 0.5 * dt;
      }

      // Elemental Infusion Visual Animations
      if (this.elementMesh) {
        this.elementMesh.rotation.y += 2.4 * dt;
        this.elementMesh.position.y = Math.sin(t * 3.2) * 0.05;
      }

      // Target acquisition and attack execution
      if (this.cooldownTimer <= 0 && activeEnemies.length > 0) {
        const target = this.findTarget();
        if (target) {
          this.currentTarget = target;

          // Smoothly rotate upper body or model towards target
          const dx = target.position.x - this.position.x;
          const dz = target.position.z - this.position.z;
          const targetAngle = Math.atan2(dx, dz);
          this.model.rotation.y = targetAngle;

          this.performAttack(target);
          const effectiveCd = (this.element === 'thunder') ? (this.cooldown / 1.5) : this.cooldown;
          this.cooldownTimer = effectiveCd;
        }
      }
    }

    findTarget() {
      const candidates = [];
      for (let i = 0; i < activeEnemies.length; i++) {
        const enemy = activeEnemies[i];
        if (enemy.isDead || enemy.reachedSanctum) continue;
        const dist = this.position.distanceTo(enemy.position);
        if (dist <= this.range) {
          candidates.push({ enemy, dist });
        }
      }

      if (candidates.length === 0) return null;

      switch (this.targetingMode) {
        case 'first':
          candidates.sort((a, b) => b.enemy.distanceTraveled - a.enemy.distanceTraveled);
          return candidates[0].enemy;
        case 'last':
          candidates.sort((a, b) => a.enemy.distanceTraveled - b.enemy.distanceTraveled);
          return candidates[0].enemy;
        case 'strongest':
          candidates.sort((a, b) => b.enemy.hp - a.enemy.hp);
          return candidates[0].enemy;
        case 'closest':
          candidates.sort((a, b) => a.dist - b.dist);
          return candidates[0].enemy;
        default:
          return candidates[0].enemy;
      }
    }

    performAttack(target) {
      this.attackAnimTimer = 0.3;

      let baseDmg = this.damage;
      if (this.element === 'earth') baseDmg = Math.round(baseDmg * 1.30); // +30% Earth dmg
      else if (this.element === 'fire') baseDmg = Math.round(baseDmg * 1.50); // +50% Fire dmg

      const elemDmgType = this.element ? (this.element.charAt(0).toUpperCase() + this.element.slice(1)) : null;

      if (this.element === 'thunder') GameState.playSound('thunderAttack');
      else if (this.element === 'earth') GameState.playSound('earthAttack');
      else if (this.element === 'fire') GameState.playSound('fireAttack');
      else if (this.element === 'water') GameState.playSound('waterAttack');

      if (this.type === 'stone') {
        // Parabolic AoE Boulder
        // Tier 3: 2.4 tiles; Tier 5: 3.2 tiles (Mega Meteor)
        let aoeRadius = 1.8;
        let isMega = false;
        if (this.level >= 5) {
          aoeRadius = 3.2;
          isMega = true;
        } else if (this.level >= 3) {
          aoeRadius = 2.4;
        }
        if (this.element === 'water') aoeRadius += 1.2;
        const dmg = isMega ? Math.round(baseDmg * 1.35) : baseDmg;
        CombatManager.launchBoulder(
          this.position.clone().add(new THREE.Vector3(0, 1.2, 0)),
          target.position.clone(),
          dmg,
          aoeRadius,
          this.element,
          elemDmgType || 'Physical'
        );
        if (!this.element) GameState.playSound('stoneThrow');
      } else if (this.type === 'oak') {
        // High-velocity slug
        // Tier 3: every 3rd shot 2x Crit; Tier 5: every 2nd shot 2.5x Crit (Twin Ballista)
        this.shotCount = (this.shotCount || 0) + 1;
        let isCrit = false;
        let critMult = 2.0;
        if (this.level >= 5) {
          isCrit = (this.shotCount % 2 === 0);
          critMult = 2.5;
        } else if (this.level >= 3) {
          isCrit = (this.shotCount % 3 === 0);
          critMult = 2.0;
        }
        const dmg = isCrit ? Math.round(baseDmg * critMult) : baseDmg;
        const muzzlePos = this.position.clone().add(new THREE.Vector3(0, 1.4, 0));
        const splashRadius = (this.element === 'water') ? 1.8 : 0;
        CombatManager.fireSlug(muzzlePos, target, dmg, isCrit, this.element, elemDmgType || 'Physical', splashRadius);
        CombatManager.spawnMuzzleFlash(muzzlePos);
        if (!this.element) GameState.playSound('oakShoot');
      } else if (this.type === 'brick') {
        // Seismic Ground Slam
        // Tier 3: 1.0s stun; Tier 5: 0.9s stun + 3.6 radius (Cataclysmic Quake)
        // Rebalanced from 1.8s to eliminate perma-stunlock
        let stunDuration = 0.7;
        let slamRadius = this.range;
        if (this.level >= 5) {
          stunDuration = 0.9;
          slamRadius = 3.6;
        } else if (this.level >= 3) {
          stunDuration = 1.0;
        }
        if (this.element === 'water') slamRadius += 1.0;
        CombatManager.triggerGroundSlam(this.position, slamRadius, baseDmg, stunDuration, this.element, elemDmgType || 'Physical');
        if (!this.element) GameState.playSound('brickSlam');
      } else if (this.type === 'diorite') {
        // Arcane Chain Beam
        // Tier 3: 3 secondary jumps (4 targets); Tier 5: 5 secondary jumps (6 targets total)
        let maxJumps = 2;
        let slowDur = 2.0;
        if (this.level >= 5) {
          maxJumps = 5;
          slowDur = 3.5;
        } else if (this.level >= 3) {
          maxJumps = 3;
          slowDur = 2.5;
        }
        if (this.element === 'water') maxJumps += 2;
        const origin = this.position.clone().add(new THREE.Vector3(0, 1.0, 0));
        CombatManager.fireChainBeam(origin, target, baseDmg, maxJumps, slowDur, this.element, elemDmgType || 'Magic');
        if (!this.element) GameState.playSound('dioriteBeam');
      }
    }

    applyElement(elemType) {
      if (this.element === elemType) return false;
      if (GameState.essence < 1) {
        FloatingTextManager.spawnText(this.position, "NEED 1 🔮 ESSENCE!", "status-resist");
        return false;
      }
      GameState.essence -= 1;
      this.element = elemType;
      this.updateElementalVisuals();
      GameState.playSound('elementInfuse');

      const names = {
        thunder: '⚡ THUNDER',
        earth: '🌿 EARTH',
        fire: '🔥 FIRE',
        water: '💧 WATER'
      };
      FloatingTextManager.spawnText(this.position, `INFUSED: ${names[elemType]}!`, `status-${elemType}`);
      updateHud();
      if (GameState.selectedGolem === this) {
        openGolemInspector(this);
      }
      return true;
    }

    updateElementalVisuals() {
      if (this.elementMesh && this.elementMesh.parent) {
        this.elementMesh.parent.remove(this.elementMesh);
        this.elementMesh = null;
      }
      if (!this.element) return;

      const group = new THREE.Group();
      if (this.element === 'thunder') {
        // Orbiting electric cyan sparks
        for (let i = 0; i < 4; i++) {
          const ang = (i / 4) * Math.PI * 2;
          const s = vox(Math.cos(ang) * 0.72, 1.1 + (i % 2) * 0.25, Math.sin(ang) * 0.72, 0.16, 0.16, 0.16, 0x00E5FF, group, 0x00E5FF, 2.8);
          s.rotation.y = Math.PI / 4;
        }
      } else if (this.element === 'earth') {
        // Orbiting mossy terracotta crags
        for (let i = 0; i < 4; i++) {
          const ang = (i / 4) * Math.PI * 2;
          vox(Math.cos(ang) * 0.8, 0.45, Math.sin(ang) * 0.8, 0.22, 0.22, 0.22, 0x5D4037, group);
          vox(Math.cos(ang) * 0.8, 0.58, Math.sin(ang) * 0.8, 0.16, 0.1, 0.16, 0x76FF03, group, 0x76FF03, 1.5);
        }
      } else if (this.element === 'fire') {
        // Floating flame crown voxels above head
        for (let i = 0; i < 4; i++) {
          const ang = (i / 4) * Math.PI * 2;
          vox(Math.cos(ang) * 0.45, 1.9 + (i % 2) * 0.2, Math.sin(ang) * 0.45, 0.18, 0.22, 0.18, 0xFF5722, group, 0xFF3D00, 3.0);
        }
      } else if (this.element === 'water') {
        // Swirling azure water droplets
        for (let i = 0; i < 4; i++) {
          const ang = (i / 4) * Math.PI * 2;
          vox(Math.cos(ang) * 0.72, 0.9 + Math.sin(ang) * 0.2, Math.sin(ang) * 0.72, 0.18, 0.18, 0.18, 0x2979FF, group, 0x40C4FF, 2.0);
        }
      }

      this.model.add(group);
      this.elementMesh = group;
    }

    getUpgradeCost() {
      const baseCost = this.config.cost;
      if (this.level === 1) return Math.round(baseCost * 0.85);
      if (this.level === 2) return Math.round(baseCost * 1.40);
      if (this.level === 3) return Math.round(baseCost * 2.20);
      if (this.level === 4) return Math.round(baseCost * 3.50);
      return 0; // Max tier (Level 5)
    }

    upgrade() {
      if (this.level >= 5) return false;
      const upgradeCost = this.getUpgradeCost();
      if (GameState.shards < upgradeCost) return false;

      GameState.shards -= upgradeCost;
      this.level++;
      this.totalInvested += upgradeCost;

      // Exact stat scaling formulas
      const dmgMult = (this.level === 5) ? 1.35 : 1.30;
      const rangeMult = (this.level === 5) ? 1.10 : 1.08;
      const cdMult = (this.level === 5) ? 0.85 : 0.88;

      this.damage = Math.round(this.damage * dmgMult);
      this.range = +(this.range * rangeMult).toFixed(2);
      this.cooldown = +(this.cooldown * cdMult).toFixed(2);

      // Evolve 3D mesh visually
      this.applyUpgradeVisuals();

      // Ascension or regular level up effects
      if (this.level === 5) {
        CombatManager.spawnAscensionSpiral(this.position.clone().add(new THREE.Vector3(0, 0.4, 0)), 36);
        GameState.playSound('ascension');
        FloatingTextManager.spawnText(this.position, "👑 PRIMAL ASCENDANCE!", "shard-reward");
      } else {
        CombatManager.spawnParticleBurst(this.position.clone().add(new THREE.Vector3(0, 1.2, 0)), 20, 0xFFD700);
        GameState.playSound('upgrade');
        const titles = ['', '', 'REINFORCED', 'AWAKENED', 'VANGUARD'];
        FloatingTextManager.spawnText(this.position, `LVL ${this.level} ${titles[this.level]}!`, "shard-reward");
      }

      updateHud();
      if (GameState.selectedGolem === this) {
        openGolemInspector(this);
        showRangeRing(this.position, this.range, this.config.color);
      }
      return true;
    }

    applyUpgradeVisuals() {
      // Level 2 (Reinforced Tier): Unique distinctive armor per golem type
      if (this.level >= 2 && !this.model.userData.lvl2Armor) {
        const lvl2Armor = new THREE.Group();
        if (this.type === 'stone') {
          // Runic Iron Bulwark: heavy iron shoulder pauldrons + emerald rune wrist bands + chest plate
          vox(-0.6, 1.12, 0, 0.42, 0.42, 0.46, C.STN_D, lvl2Armor);
          vox( 0.6, 1.12, 0, 0.42, 0.42, 0.46, C.STN_D, lvl2Armor);
          vox(-0.6, 1.34, 0, 0.22, 0.1,  0.22, C.STN_L, lvl2Armor);
          vox( 0.6, 1.34, 0, 0.22, 0.1,  0.22, C.STN_L, lvl2Armor);
          vox(-0.65, 0.5, 0.05, 0.22, 0.28, 0.24, C.GLOW_GRN, lvl2Armor, C.GLOW_GRN, 1.8);
          vox( 0.65, 0.5, 0.05, 0.22, 0.28, 0.24, C.GLOW_GRN, lvl2Armor, C.GLOW_GRN, 1.8);
          vox(0, 0.9, 0.32, 0.4, 0.35, 0.15, C.STN_D, lvl2Armor);
        } else if (this.type === 'oak') {
          // Amber Bark Ranger: polished golden-amber pauldrons & leaf blades
          vox(-0.55, 1.15, 0, 0.36, 0.38, 0.38, C.OG_MTL, lvl2Armor);
          vox( 0.55, 1.15, 0, 0.36, 0.38, 0.38, C.OG_MTL, lvl2Armor);
          vox(-0.68, 1.25, 0, 0.12, 0.3,  0.25, 0x2E8B57, lvl2Armor);
          vox( 0.68, 1.25, 0, 0.12, 0.3,  0.25, 0x2E8B57, lvl2Armor);
          vox(0, 0.95, 0.28, 0.35, 0.45, 0.12, C.FLOWER_Y, lvl2Armor, C.FLOWER_Y, 0.8);
        } else if (this.type === 'brick') {
          // Ironbound Bruiser: heavy riveted iron gauntlets & molten mortar seams
          vox(-0.68, 0.3, 0.08, 0.45, 0.42, 0.48, C.BG_SL_DK, lvl2Armor);
          vox( 0.68, 0.3, 0.08, 0.45, 0.42, 0.48, C.BG_SL_DK, lvl2Armor);
          vox(-0.55, 1.15, 0, 0.38, 0.38, 0.42, C.BG_SL, lvl2Armor);
          vox( 0.55, 1.15, 0, 0.38, 0.38, 0.42, C.BG_SL, lvl2Armor);
          vox(0, 0.8, 0.32, 0.5, 0.08, 0.08, 0xFF5500, lvl2Armor, 0xFF5500, 2.2);
        } else if (this.type === 'diorite') {
          // Solar Sentinel: polished gold brow visor & floating wrist prism shards
          vox(0, 1.68, 0.25, 0.52, 0.15, 0.2, C.DG_GLD, lvl2Armor, C.DG_GLD, 1.5);
          vox(-0.62, 0.55, 0.1, 0.16, 0.28, 0.16, C.DG_GLD, lvl2Armor, C.DG_GLD, 2.0);
          vox( 0.62, 0.55, 0.1, 0.16, 0.28, 0.16, C.DG_GLD, lvl2Armor, C.DG_GLD, 2.0);
          vox(0, 1.0, 0.28, 0.28, 0.28, 0.15, C.DG_GLD, lvl2Armor, C.DG_GLD, 1.6);
        }
        this.model.add(lvl2Armor);
        this.model.userData.lvl2Armor = lvl2Armor;
      }

      // Level 3 (Awakened Tier): Thematic major awakening enhancements
      if (this.level >= 3 && !this.model.userData.awakenedVisual) {
        const awkGroup = new THREE.Group();
        if (this.type === 'stone') {
          // Floating shoulder crag boulders bobbing in air + emerald heart
          const crags = new THREE.Group();
          vox(-0.75, 1.5, 0, 0.42, 0.45, 0.42, C.SG_M, crags);
          vox(-0.75, 1.74, 0, 0.25, 0.15, 0.25, C.MOSS, crags);
          vox( 0.75, 1.5, 0, 0.42, 0.45, 0.42, C.SG_M, crags);
          vox( 0.75, 1.74, 0, 0.25, 0.15, 0.25, C.MOSS, crags);
          awkGroup.add(crags);
          this.model.userData.stoneCrags = crags;

          // Glowing emerald heart core
          vox(0, 0.9, 0.32, 0.24, 0.24, 0.22, C.GLOW_GRN, awkGroup, C.GLOW_GRN, 2.6);
          // Spiked brow
          vox(0, 1.75, 0.26, 0.48, 0.16, 0.2, C.SG_DK, awkGroup);
        } else if (this.type === 'oak') {
          // Branching wooden stag antlers with blooming cherry blossoms
          const antlers = new THREE.Group();
          antlers.position.set(0, 1.75, 0);
          // Left antler branch
          vox(-0.25, 0.25, 0, 0.12, 0.45, 0.12, C.OG_WD_DK, antlers);
          vox(-0.45, 0.55, 0, 0.35, 0.12, 0.12, C.OG_WD, antlers);
          vox(-0.55, 0.75, 0, 0.12, 0.35, 0.12, C.OG_WD, antlers);
          vox(-0.55, 0.95, 0, 0.18, 0.16, 0.18, 0xFFB7C5, antlers, 0xFFB7C5, 1.2);
          vox(-0.35, 0.65, 0.1, 0.14, 0.14, 0.14, 0x32CD32, antlers);
          // Right antler branch
          vox( 0.25, 0.25, 0, 0.12, 0.45, 0.12, C.OG_WD_DK, antlers);
          vox( 0.45, 0.55, 0, 0.35, 0.12, 0.12, C.OG_WD, antlers);
          vox( 0.55, 0.75, 0, 0.12, 0.35, 0.12, C.OG_WD, antlers);
          vox( 0.55, 0.95, 0, 0.18, 0.16, 0.18, 0xFFB7C5, antlers, 0xFFB7C5, 1.2);
          vox( 0.35, 0.65, 0.1, 0.14, 0.14, 0.14, 0x32CD32, antlers);
          awkGroup.add(antlers);
          this.model.userData.stagAntlers = antlers;

          // Glowing emerald spirit core
          vox(0, 0.95, 0.3, 0.22, 0.22, 0.2, C.GLOW_GRN, awkGroup, C.GLOW_GRN, 2.4);
        } else if (this.type === 'brick') {
          // Twin smoking cast-iron exhaust smokestacks & heavy blast visor
          vox(-0.4, 1.6, -0.3, 0.26, 0.6, 0.26, C.BG_SL_DK, awkGroup);
          vox( 0.4, 1.6, -0.3, 0.26, 0.6, 0.26, C.BG_SL_DK, awkGroup);
          vox(-0.4, 1.95, -0.3, 0.16, 0.16, 0.16, 0xFF3300, awkGroup, 0xFF3300, 2.5);
          vox( 0.4, 1.95, -0.3, 0.16, 0.16, 0.16, 0xFF3300, awkGroup, 0xFF3300, 2.5);
          vox(0, 1.65, 0.25, 0.55, 0.18, 0.18, C.BG_SL, awkGroup);
          vox(0, 1.65, 0.32, 0.42, 0.08, 0.06, 0xFF5500, awkGroup, 0xFF5500, 2.2);
        } else if (this.type === 'diorite') {
          // 3D Celestial Astrolabe gyroscope floating above head
          const astrolabe = new THREE.Group();
          astrolabe.position.set(0, 2.0, 0);

          const astroOuter = new THREE.Group();
          for (let i = 0; i < 8; i++) {
            const ang = (i / 8) * Math.PI * 2;
            vox(Math.cos(ang) * 0.42, 0, Math.sin(ang) * 0.42, 0.09, 0.09, 0.09, C.DG_GLD, astroOuter, C.DG_GLD, 2.4);
          }
          astrolabe.add(astroOuter);

          const astroInner = new THREE.Group();
          astroInner.rotation.x = Math.PI / 4;
          for (let i = 0; i < 6; i++) {
            const ang = (i / 6) * Math.PI * 2;
            vox(Math.cos(ang) * 0.28, 0, Math.sin(ang) * 0.28, 0.08, 0.08, 0.08, 0xFFFFFF, astroInner, 0xFFFFFF, 2.5);
          }
          astrolabe.add(astroInner);

          // Brilliant sun gem in center
          vox(0, 0, 0, 0.15, 0.15, 0.15, 0xFFD700, astrolabe, 0xFFD700, 3.0);
          awkGroup.add(astrolabe);
          this.model.userData.astrolabe = astrolabe;
          this.model.userData.astrolabeOuter = astroOuter;
          this.model.userData.astrolabeInner = astroInner;
        }

        // Generic fallback halo if not diorite
        if (!this.model.userData.halo) {
          const halo = new THREE.Group();
          halo.position.set(0, 1.9, 0);
          const count = 8;
          const r = 0.42;
          for (let i = 0; i < count; i++) {
            const ang = (i / count) * Math.PI * 2;
            const col = (i % 2 === 0) ? C.DG_GLD : C.GLOW_GRN;
            vox(Math.cos(ang) * r, 0, Math.sin(ang) * r, 0.1, 0.1, 0.1, col, halo, col, 2.5);
          }
          awkGroup.add(halo);
          this.model.userData.halo = halo;
        }

        this.model.add(awkGroup);
        this.model.userData.awakenedVisual = awkGroup;
      }

      // Level 4 (Primal Vanguard): Heavy armaments & elite upgrades
      if (this.level >= 4 && !this.model.userData.lvl4Vanguard) {
        const vGroup = new THREE.Group();
        if (this.type === 'stone') {
          // Dorsal obsidian crag spines + glowing lava fissures on chest/fists
          vox(0, 1.45, -0.4, 0.5, 0.9, 0.32, C.SG_DK, vGroup);
          vox(-0.38, 1.25, -0.35, 0.3, 0.7, 0.28, C.SG_M, vGroup);
          vox( 0.38, 1.25, -0.35, 0.3, 0.7, 0.28, C.SG_M, vGroup);
          // Molten magma fissures
          vox(0, 0.7, 0.33, 0.12, 0.55, 0.06, 0xFF4500, vGroup, 0xFF4500, 2.4);
          vox(-0.68, 0.3, 0.12, 0.26, 0.26, 0.26, 0xFF4500, vGroup, 0xFF4500, 2.2);
          vox( 0.68, 0.3, 0.12, 0.26, 0.26, 0.26, 0xFF4500, vGroup, 0xFF4500, 2.2);
        } else if (this.type === 'oak') {
          // Quadruple shoulder ballistas with nature spirit bowstrings
          vox(-0.45, 1.55, -0.28, 0.16, 0.16, 0.75, C.OG_MTL, vGroup);
          vox( 0.45, 1.55, -0.28, 0.16, 0.16, 0.75, C.OG_MTL, vGroup);
          vox(-0.45, 1.55,  0.18, 0.4,  0.1,  0.12, C.OG_WD_DK, vGroup);
          vox( 0.45, 1.55,  0.18, 0.4,  0.1,  0.12, C.OG_WD_DK, vGroup);
          vox(-0.45, 1.55,  0.22, 0.44, 0.04, 0.04, 0x39FF14, vGroup, 0x39FF14, 2.2);
          vox( 0.45, 1.55,  0.22, 0.44, 0.04, 0.04, 0x39FF14, vGroup, 0x39FF14, 2.2);
        } else if (this.type === 'brick') {
          // Dual hydraulic steam pistons with brass fittings & molten crucible furnace door
          vox(-0.75, 0.8, 0, 0.18, 0.55, 0.18, C.OG_MTL, vGroup);
          vox( 0.75, 0.8, 0, 0.18, 0.55, 0.18, C.OG_MTL, vGroup);
          vox(-0.75, 1.1, 0, 0.24, 0.14, 0.24, 0xD4AF37, vGroup);
          vox( 0.75, 1.1, 0, 0.24, 0.14, 0.24, 0xD4AF37, vGroup);
          vox(0, 0.9, 0.34, 0.36, 0.36, 0.14, 0xFF3300, vGroup, 0xFF3300, 2.8);
          vox(0, 0.9, 0.42, 0.42, 0.42, 0.05, C.BG_SL_DK, vGroup);
        } else if (this.type === 'diorite') {
          // Dual floating crystal prism pylons hovering beside shoulders
          const pylons = new THREE.Group();
          pylons.position.set(0, 1.25, 0);
          vox(-0.85, 0, 0, 0.18, 0.65, 0.18, C.DG_GLD, pylons, C.DG_GLD, 2.5);
          vox(-0.85, 0, 0, 0.26, 0.2,  0.26, 0xFFFFFF, pylons, 0xFFFFFF, 2.8);
          vox( 0.85, 0, 0, 0.18, 0.65, 0.18, C.DG_GLD, pylons, C.DG_GLD, 2.5);
          vox( 0.85, 0, 0, 0.26, 0.2,  0.26, 0xFFFFFF, pylons, 0xFFFFFF, 2.8);
          vGroup.add(pylons);
          this.model.userData.prismPylons = pylons;

          // Golden filigree shoulder wings
          vox(-0.7, 1.35, -0.15, 0.45, 0.12, 0.5, C.DG_GLD, vGroup, C.DG_GLD, 1.4);
          vox( 0.7, 1.35, -0.15, 0.45, 0.12, 0.5, C.DG_GLD, vGroup, C.DG_GLD, 1.4);
        }
        this.model.add(vGroup);
        this.model.userData.lvl4Vanguard = vGroup;
      }

      // Level 5 (Ascended Titan - Primal Ascendance): Colossal majestic transformation
      if (this.level >= 5 && !this.model.userData.ascended) {
        const ascGroup = new THREE.Group();

        if (this.type === 'stone') {
          // Primal Earth Colossus: 4 tumbling asteroid boulders orbiting waist + monolithic magma crown
          const asteroids = new THREE.Group();
          asteroids.position.set(0, 0.95, 0);
          for (let i = 0; i < 4; i++) {
            const ang = (i / 4) * Math.PI * 2;
            const ast = new THREE.Group();
            ast.position.set(Math.cos(ang) * 0.82, 0, Math.sin(ang) * 0.82);
            vox(0, 0, 0, 0.28, 0.28, 0.28, C.SG_DK, ast);
            vox(0.08, 0.08, 0, 0.18, 0.18, 0.18, C.MOSS, ast);
            vox(0, 0, 0.1, 0.12, 0.12, 0.12, 0xFF4500, ast, 0xFF4500, 2.4);
            asteroids.add(ast);
          }
          ascGroup.add(asteroids);
          this.model.userData.ascOrbitAsteroids = asteroids;

          // Magma stone crown
          const crown = new THREE.Group();
          crown.position.set(0, 2.15, 0);
          for (let i = 0; i < 6; i++) {
            const ang = (i / 6) * Math.PI * 2;
            vox(Math.cos(ang) * 0.42, 0, Math.sin(ang) * 0.42, 0.14, 0.25, 0.14, C.SG_DK, crown);
            vox(Math.cos(ang) * 0.42, 0.18, Math.sin(ang) * 0.42, 0.1, 0.1, 0.1, 0xFF5500, crown, 0xFF5500, 2.6);
          }
          ascGroup.add(crown);
          this.model.userData.ascCrownOuter = crown;

        } else if (this.type === 'oak') {
          // Avatar of Yggdrasil: Blooming golden-emerald sakura canopy + 6 orbiting spirit wisps
          const canopy = new THREE.Group();
          canopy.position.set(0, 2.2, 0);
          vox(0, 0.15, 0, 0.85, 0.28, 0.85, 0x50C878, canopy);
          vox(0, 0.35, 0, 0.65, 0.25, 0.65, 0xFFD700, canopy, 0xFFD700, 1.4);
          vox(-0.35, 0.2, 0.2, 0.3, 0.2, 0.3, 0xFFB7C5, canopy, 0xFFB7C5, 1.2);
          vox( 0.35, 0.2, -0.2, 0.3, 0.2, 0.3, 0xFFB7C5, canopy, 0xFFB7C5, 1.2);
          ascGroup.add(canopy);
          this.model.userData.ascCrownOuter = canopy;

          // 6 orbiting spirit wisps
          const wisps = new THREE.Group();
          wisps.position.set(0, 1.1, 0);
          for (let i = 0; i < 6; i++) {
            const ang = (i / 6) * Math.PI * 2;
            vox(Math.cos(ang) * 0.78, 0, Math.sin(ang) * 0.78, 0.12, 0.12, 0.12, (i%2===0 ? 0x50C878 : 0xFFB7C5), wisps, (i%2===0 ? 0x50C878 : 0xFFB7C5), 2.8);
          }
          ascGroup.add(wisps);
          this.model.userData.ascOrbitWisps = wisps;

        } else if (this.type === 'brick') {
          // Cataclysmic Forge Titan: Smelting blast chimneys + 6 infernal cinder asteroids + anvil crown
          const forgeCh = new THREE.Group();
          vox(-0.45, 1.8, -0.32, 0.32, 0.9, 0.32, C.BG_SL_DK, forgeCh);
          vox( 0.45, 1.8, -0.32, 0.32, 0.9, 0.32, C.BG_SL_DK, forgeCh);
          vox(-0.45, 2.3, -0.32, 0.22, 0.25, 0.22, 0xFF3300, forgeCh, 0xFF3300, 3.0);
          vox( 0.45, 2.3, -0.32, 0.22, 0.25, 0.22, 0xFF3300, forgeCh, 0xFF3300, 3.0);
          ascGroup.add(forgeCh);

          // Anvil magma crown
          const anvilCr = new THREE.Group();
          anvilCr.position.set(0, 2.2, 0);
          vox(0, 0, 0, 0.75, 0.18, 0.45, C.BG_SL, anvilCr);
          vox(0, 0.15, 0, 0.5, 0.12, 0.35, 0xFF4500, anvilCr, 0xFF4500, 2.6);
          ascGroup.add(anvilCr);
          this.model.userData.ascCrownOuter = anvilCr;

          // 6 orbiting burning cinders
          const cinders = new THREE.Group();
          cinders.position.set(0, 0.9, 0);
          for (let i = 0; i < 6; i++) {
            const ang = (i / 6) * Math.PI * 2;
            vox(Math.cos(ang) * 0.75, 0, Math.sin(ang) * 0.75, 0.14, 0.14, 0.14, 0xFF3300, cinders, 0xFF5500, 3.0);
          }
          ascGroup.add(cinders);
          this.model.userData.ascOrbitCinders = cinders;

        } else if (this.type === 'diorite') {
          // Cosmic Chronos Solar Sovereign: Sacred geometry solar mandala disk + 6 orbiting star prisms
          const mandala = new THREE.Group();
          mandala.position.set(0, 1.4, -0.35);
          for (let i = 0; i < 12; i++) {
            const ang = (i / 12) * Math.PI * 2;
            vox(Math.cos(ang) * 0.7, Math.sin(ang) * 0.7, 0, 0.1, 0.1, 0.06, C.DG_GLD, mandala, C.DG_GLD, 2.4);
          }
          for (let i = 0; i < 8; i++) {
            const ang = (i / 8) * Math.PI * 2;
            vox(Math.cos(ang) * 0.45, Math.sin(ang) * 0.45, 0.02, 0.08, 0.08, 0.06, 0xFFFFFF, mandala, 0xFFFFFF, 2.5);
          }
          ascGroup.add(mandala);
          this.model.userData.ascSolarMandala = mandala;

          // Solar crown
          const sCrown = new THREE.Group();
          sCrown.position.set(0, 2.25, 0);
          for (let i = 0; i < 8; i++) {
            const ang = (i / 8) * Math.PI * 2;
            vox(Math.cos(ang) * 0.48, 0, Math.sin(ang) * 0.48, 0.1, 0.2, 0.1, 0xFFD700, sCrown, 0xFFD700, 3.0);
          }
          ascGroup.add(sCrown);
          this.model.userData.ascCrownOuter = sCrown;

          // 6 orbiting geometric star octahedrons
          const stars = new THREE.Group();
          stars.position.set(0, 1.1, 0);
          for (let i = 0; i < 6; i++) {
            const ang = (i / 6) * Math.PI * 2;
            const star = vox(Math.cos(ang) * 0.85, 0, Math.sin(ang) * 0.85, 0.15, 0.15, 0.15, (i%2===0 ? 0xFFD700 : 0x00F5D4), stars, (i%2===0 ? 0xFFD700 : 0x00F5D4), 2.8);
            star.rotation.y = Math.PI / 4;
            star.rotation.z = Math.PI / 4;
          }
          ascGroup.add(stars);
          this.model.userData.ascOrbitStars = stars;
        }

        // Luminous ground pedestal rune aura ring
        const auraColor = (this.type === 'brick') ? 0xFF3300 : ((this.type === 'oak' || this.type === 'stone') ? 0x39FF14 : 0xFFD700);
        const auraGeo = new THREE.RingGeometry(0.35, 0.8, 24);
        const auraMat = new THREE.MeshBasicMaterial({
          color: auraColor,
          transparent: true,
          opacity: 0.7,
          side: THREE.DoubleSide
        });
        const auraMesh = new THREE.Mesh(auraGeo, auraMat);
        auraMesh.rotation.x = -Math.PI / 2;
        auraMesh.position.set(0, -0.62, 0);
        ascGroup.add(auraMesh);

        // Radiant head point light
        const ascLight = new THREE.PointLight(auraColor, 1.5, 4.5);
        ascLight.position.set(0, 2.1, 0);
        ascGroup.add(ascLight);

        this.model.add(ascGroup);
        this.model.userData.ascended = ascGroup;
        this.model.userData.ascAura = auraMesh;
      }
    }

    sell() {
      const refund = Math.round(this.totalInvested * 0.70);
      GameState.addShards(refund);

      // Remove 3D model
      if (this.model && this.model.parent) {
        this.model.parent.remove(this.model);
      }

      // Free pedestal
      this.pedestal.golem = null;

      // Remove from active list
      const idx = activeGolems.indexOf(this);
      if (idx !== -1) activeGolems.splice(idx, 1);

      CombatManager.spawnParticleBurst(this.position, 16, C.STN_M);
      GameState.playSound('sell');

      GameState.deselect();
      updateHud();
    }

    setTargetingMode(mode) {
      this.targetingMode = mode;
      if (GameState.selectedGolem === this) {
        updateTargetingButtons(mode);
      }
    }
  }

  function summonGolem(ped, type) {
    type = type || GameState.selectedGolemType;
    if (!ped || ped.golem) return null;
    const cfg = GOLEM_CONFIGS[type];
    if (GameState.shards >= cfg.cost) {
      GameState.shards -= cfg.cost;
      updateHud();
      const golem = new GolemInstance(type, ped);
      GameState.selectPedestal(ped);
      GameState.playSound('summon');
      return golem;
    } else {
      GameState.playSound('error');
      return null;
    }
  }

  // ========================================================
  // PROCEDURAL ALIEN ENEMY MODELS & CLASS
  // ========================================================

  function createAlienScoutModel() {
    const g = new THREE.Group();
    // Central obsidian aerodynamic fuselage
    vox(0, 0.45, 0, 0.6, 0.32, 0.9, C.AL_OBSID, g);
    // Dorsal amethyst crest plate
    vox(0, 0.62, -0.05, 0.35, 0.16, 0.6, C.AL_CHITIN_D, g);
    vox(0, 0.72, -0.15, 0.18, 0.14, 0.35, C.AL_CHITIN_L, g);

    // Glowing bright cyan horizontal sensor visor
    vox(0, 0.45, 0.44, 0.42, 0.14, 0.12, C.AL_CYAN_BRT, g, C.AL_CYAN_BRT, 2.5);
    // Dual forward plasma needle probes
    vox(-0.18, 0.45, 0.6, 0.08, 0.08, 0.35, C.AL_ALLOY, g);
    vox( 0.18, 0.45, 0.6, 0.08, 0.08, 0.35, C.AL_ALLOY, g);

    // Swept manta wings with cyan bio-conduit striping
    vox(-0.55, 0.48, -0.08, 0.55, 0.08, 0.75, C.AL_VOID_M, g);
    vox( 0.55, 0.48, -0.08, 0.55, 0.08, 0.75, C.AL_VOID_M, g);
    vox(-0.85, 0.52, -0.15, 0.35, 0.06, 0.5, C.AL_CHITIN_D, g);
    vox( 0.85, 0.52, -0.15, 0.35, 0.06, 0.5, C.AL_CHITIN_D, g);

    // Glowing electric cyan wing edge conduits
    vox(-0.7, 0.5, 0.25, 0.5, 0.08, 0.08, C.AL_CYAN_NEON, g, C.AL_CYAN_NEON, 2.0);
    vox( 0.7, 0.5, 0.25, 0.5, 0.08, 0.08, C.AL_CYAN_NEON, g, C.AL_CYAN_NEON, 2.0);

    // Ventral anti-grav thruster core
    vox(0, 0.28, -0.1, 0.3, 0.08, 0.35, C.AL_CYAN_NEON, g, C.AL_CYAN_NEON, 2.4);

    g.scale.setScalar(0.72);
    return g;
  }

  function createVoidTrooperModel() {
    const g = new THREE.Group();
    // Segmented armored legs
    const legL = new THREE.Group();
    vox(-0.28, 0.45, 0, 0.22, 0.85, 0.24, C.AL_VOID_DK, legL);
    vox(-0.28, 0.5, 0.12, 0.24, 0.22, 0.12, C.AL_CHITIN_D, legL);
    vox(-0.28, 0.1, 0.08, 0.24, 0.2, 0.35, C.AL_OBSID, legL);
    g.add(legL);

    const legR = new THREE.Group();
    vox( 0.28, 0.45, 0, 0.22, 0.85, 0.24, C.AL_VOID_DK, legR);
    vox( 0.28, 0.5, 0.12, 0.24, 0.22, 0.12, C.AL_CHITIN_D, legR);
    vox( 0.28, 0.1, 0.08, 0.24, 0.2, 0.35, C.AL_OBSID, legR);
    g.add(legR);

    // Armored torso with ribbed underbelly & royal purple carapace
    vox(0, 1.15, 0, 0.75, 0.8, 0.48, C.AL_CHITIN_D, g);
    vox(0, 1.15, 0.22, 0.5, 0.65, 0.12, C.AL_BELLY, g);
    // Glowing plasma magenta biomarker core
    vox(0, 1.2, 0.27, 0.28, 0.32, 0.08, C.AL_MAG_NEON, g, C.AL_MAG_NEON, 2.2);

    // Tiered iridescent shoulder pauldrons
    vox(-0.52, 1.35, 0, 0.35, 0.35, 0.42, C.AL_CHITIN_L, g);
    vox( 0.52, 1.35, 0, 0.35, 0.35, 0.42, C.AL_CHITIN_L, g);
    vox(-0.55, 1.48, 0, 0.15, 0.15, 0.35, C.AL_MAG_NEON, g, C.AL_MAG_NEON, 1.8);
    vox( 0.55, 1.48, 0, 0.15, 0.15, 0.35, C.AL_MAG_NEON, g, C.AL_MAG_NEON, 1.8);

    // Dual serrated chitin mantis blade arms angled forward
    vox(-0.5, 0.9, 0.25, 0.16, 0.55, 0.18, C.AL_VOID_M, g);
    vox( 0.5, 0.9, 0.25, 0.16, 0.55, 0.18, C.AL_VOID_M, g);
    // Forward blade scythes with neon magenta edges
    vox(-0.5, 0.65, 0.45, 0.12, 0.45, 0.35, C.AL_OBSID, g);
    vox( 0.5, 0.65, 0.45, 0.12, 0.45, 0.35, C.AL_OBSID, g);
    vox(-0.5, 0.65, 0.62, 0.08, 0.4,  0.1,  C.AL_MAG_NEON, g, C.AL_MAG_NEON, 2.4);
    vox( 0.5, 0.65, 0.62, 0.08, 0.4,  0.1,  C.AL_MAG_NEON, g, C.AL_MAG_NEON, 2.4);

    // Horned insectoid helm with dual glowing magenta slit eyes
    vox(0, 1.75, 0, 0.5, 0.48, 0.5, C.AL_OBSID, g);
    vox(0, 1.95, -0.05, 0.35, 0.2, 0.4, C.AL_CHITIN_L, g);
    vox(-0.25, 2.1, 0, 0.1, 0.3, 0.1, C.AL_CHITIN_D, g);
    vox( 0.25, 2.1, 0, 0.1, 0.3, 0.1, C.AL_CHITIN_D, g);
    vox(-0.15, 1.76, 0.26, 0.14, 0.12, 0.08, C.AL_MAG_BRT, g, C.AL_MAG_BRT, 2.5);
    vox( 0.15, 1.76, 0.26, 0.14, 0.12, 0.08, C.AL_MAG_BRT, g, C.AL_MAG_BRT, 2.5);

    g.scale.setScalar(0.7);
    g.userData.legL = legL;
    g.userData.legR = legR;
    return g;
  }

  function createPhaseShielderModel() {
    const g = new THREE.Group();
    // Heavy armored quadruped legs
    vox(-0.45, 0.4, -0.3, 0.32, 0.8, 0.35, C.AL_VOID_DK, g);
    vox( 0.45, 0.4, -0.3, 0.32, 0.8, 0.35, C.AL_VOID_DK, g);
    vox(-0.45, 0.4,  0.3, 0.32, 0.8, 0.35, C.AL_VOID_DK, g);
    vox( 0.45, 0.4,  0.3, 0.32, 0.8, 0.35, C.AL_VOID_DK, g);

    // Heavy gold armored foot caps
    vox(-0.45, 0.1, -0.3, 0.36, 0.2, 0.4, C.AL_GOLD_ARM, g);
    vox( 0.45, 0.1, -0.3, 0.36, 0.2, 0.4, C.AL_GOLD_ARM, g);
    vox(-0.45, 0.1,  0.3, 0.36, 0.2, 0.4, C.AL_GOLD_ARM, g);
    vox( 0.45, 0.1,  0.3, 0.36, 0.2, 0.4, C.AL_GOLD_ARM, g);

    // Thick tortoise shell carapace back with glowing neon cyan spine
    vox(0, 1.25, 0, 1.2, 0.9, 1.1, C.AL_OBSID, g);
    vox(0, 1.55, -0.05, 0.95, 0.45, 0.9, C.AL_CHITIN_D, g);
    vox(0, 1.75, -0.08, 0.65, 0.25, 0.7, C.AL_CHITIN_L, g);

    // Glowing cyan energy spine conduits
    vox(0, 1.6, -0.05, 0.16, 0.42, 0.92, C.AL_CYAN_NEON, g, C.AL_CYAN_NEON, 2.4);
    vox(0, 1.2, -0.56, 0.6, 0.6, 0.1, C.AL_GOLD_ARM, g);

    // Front head / heavy visor
    vox(0, 1.2, 0.58, 0.55, 0.45, 0.4, C.AL_VOID_M, g);
    vox(0, 1.2, 0.78, 0.42, 0.14, 0.08, C.AL_CYAN_BRT, g, C.AL_CYAN_BRT, 2.4);

    // Massive glowing translucent hexagonal Phase Riot Shield
    const shieldMesh = vox(0, 1.2, 1.0, 1.6, 1.6, 0.1, C.AL_CYAN_NEON, g, C.AL_CYAN_NEON, 1.8, 0.62);
    // Heavy shield perimeter frame with gold corner brackets
    vox(0, 1.95, 1.0, 1.7, 0.18, 0.16, C.AL_GOLD_ARM, g);
    vox(0, 0.45, 1.0, 1.7, 0.18, 0.16, C.AL_GOLD_ARM, g);
    vox(-0.8, 1.2, 1.0, 0.18, 1.5, 0.16, C.AL_GOLD_ARM, g);
    vox( 0.8, 1.2, 1.0, 0.18, 1.5, 0.16, C.AL_GOLD_ARM, g);
    vox(0, 1.2, 1.04, 0.4, 0.4, 0.1, C.AL_CYAN_BRT, g, C.AL_CYAN_BRT, 2.5);

    g.scale.setScalar(0.72);
    g.userData.shield = shieldMesh;
    return g;
  }

  function createSwarmSkittererModel() {
    const g = new THREE.Group();
    // Segmented cephalothorax of deep obsidian void
    vox(0, 0.35, 0.15, 0.52, 0.32, 0.5, C.AL_VOID_DK, g);
    vox(0, 0.48, 0.15, 0.35, 0.16, 0.38, C.AL_CHITIN_D, g);

    // Swollen toxic bio-plasma abdomen glowing radioactive lime
    const acidSac = vox(0, 0.45, -0.42, 0.72, 0.55, 0.82, C.AL_ACID, g, C.AL_ACID, 1.8);
    // Dark chitin veins across acid sac
    vox(0, 0.65, -0.42, 0.14, 0.18, 0.84, C.AL_VOID_DK, g);
    vox(0, 0.45, -0.42, 0.74, 0.14, 0.14, C.AL_VOID_DK, g);

    // Glowing venom fangs & acid eyes
    vox(-0.16, 0.32, 0.45, 0.1, 0.16, 0.18, C.AL_ACID, g, C.AL_ACID, 2.4);
    vox( 0.16, 0.32, 0.45, 0.1, 0.16, 0.18, C.AL_ACID, g, C.AL_ACID, 2.4);
    vox(-0.12, 0.45, 0.38, 0.1, 0.1, 0.1, C.AL_MAG_BRT, g, C.AL_MAG_BRT, 2.2);
    vox( 0.12, 0.45, 0.38, 0.1, 0.1, 0.1, C.AL_MAG_BRT, g, C.AL_MAG_BRT, 2.2);

    // 6 articulated jointed arachnid scuttling legs
    const legs = [];
    const legOffsets = [
      [-0.45, 0.22,  0.35, -1],
      [ 0.45, 0.22,  0.35,  1],
      [-0.52, 0.22,  0.0,  -1],
      [ 0.52, 0.22,  0.0,   1],
      [-0.45, 0.22, -0.35, -1],
      [ 0.45, 0.22, -0.35,  1],
    ];
    legOffsets.forEach(lo => {
      const legGroup = new THREE.Group();
      legGroup.position.set(lo[0], lo[1], lo[2]);
      vox(lo[3] * 0.15, 0.15, 0, 0.32, 0.1, 0.12, C.AL_CHITIN_D, legGroup);
      vox(lo[3] * 0.32, -0.05, 0, 0.12, 0.35, 0.1, C.AL_OBSID, legGroup);
      g.add(legGroup);
      legs.push(legGroup);
    });

    g.scale.setScalar(0.72);
    g.userData.legs = legs;
    g.userData.acidSac = acidSac;
    return g;
  }

  function createAstralLeviathanBossModel() {
    const g = new THREE.Group();

    // 1. Serpentine Void Leviathan Multi-Segment Body
    // Tail base resting on path
    vox(0, 0.4, -0.8, 1.4, 0.8, 1.6, C.AL_OBSID, g);
    vox(0, 0.8, -0.9, 0.9, 0.4, 1.2, C.AL_CHITIN_D, g);

    // Mid-section rising up
    vox(0, 1.3, -0.3, 1.7, 1.2, 1.5, C.AL_VOID_DK, g);
    vox(0, 1.4, -0.3, 1.8, 0.3, 1.6, C.AL_CHITIN_L, g);

    // Upper Torso / Armored Mantis Chassis
    vox(0, 2.4, 0.1, 2.0, 1.4, 1.6, C.AL_CHITIN_D, g);
    // Dorsal spine fin crests
    vox(0, 2.6, -0.75, 0.28, 1.8, 0.7, C.AL_CHITIN_L, g);
    vox(0, 3.4, -0.5,  0.2,  1.0, 0.5, C.AL_MAG_NEON, g, C.AL_MAG_NEON, 2.2);

    // Ribbed glowing magenta underbelly plates
    vox(0, 2.3, 0.85, 1.3, 1.2, 0.2, C.AL_BELLY, g);
    vox(0, 2.3, 0.96, 0.9, 0.9, 0.08, C.AL_MAG_NEON, g, C.AL_MAG_NEON, 2.0);

    // 2. Pulsating Antimatter Singularity Core (in center of chest)
    const core = new THREE.Group();
    core.position.set(0, 2.35, 0.98);
    vox(0, 0, 0, 0.7, 0.7, 0.3, C.AL_MAG_NEON, core, C.AL_MAG_NEON, 2.5);
    vox(0, 0, 0.08, 0.45, 0.45, 0.25, C.AL_MAG_BRT, core, C.AL_MAG_BRT, 3.2);
    vox(0, 0, 0.16, 0.2, 0.2, 0.15, 0xFFFFFF, core, 0xFFFFFF, 3.5);
    g.add(core);

    // 3. Dual Colossal Cyber-Mantis Scythes mounted on shoulders
    const scytheL = new THREE.Group();
    scytheL.position.set(-1.1, 2.6, 0.2);
    vox(-0.35, 0, 0, 0.65, 0.45, 0.5, C.AL_ALLOY, scytheL);
    vox(-0.6, -0.4, 0.2, 0.4, 0.8, 0.4, C.AL_CHITIN_D, scytheL);
    // Heavy forward scythe blade
    vox(-0.6, -0.7, 0.9, 0.25, 0.45, 1.4, C.AL_OBSID, scytheL);
    vox(-0.6, -0.7, 1.3, 0.12, 0.4,  0.8, C.AL_MAG_BRT, scytheL, C.AL_MAG_BRT, 2.8);
    g.add(scytheL);

    const scytheR = new THREE.Group();
    scytheR.position.set( 1.1, 2.6, 0.2);
    vox( 0.35, 0, 0, 0.65, 0.45, 0.5, C.AL_ALLOY, scytheR);
    vox( 0.6, -0.4, 0.2, 0.4, 0.8, 0.4, C.AL_CHITIN_D, scytheR);
    // Heavy forward scythe blade
    vox( 0.6, -0.7, 0.9, 0.25, 0.45, 1.4, C.AL_OBSID, scytheR);
    vox( 0.6, -0.7, 1.3, 0.12, 0.4,  0.8, C.AL_MAG_BRT, scytheR, C.AL_MAG_BRT, 2.8);
    g.add(scytheR);

    // 4. Crowned Eldritch Head with 5 Eyes
    const head = new THREE.Group();
    head.position.set(0, 3.4, 0.25);
    vox(0, 0, 0, 1.2, 0.85, 1.2, C.AL_OBSID, head);
    vox(0, 0.45, -0.1, 0.95, 0.45, 1.1, C.AL_CHITIN_L, head);
    // Crown horns
    vox(-0.6, 0.75, 0, 0.2, 0.65, 0.2, C.AL_CHITIN_D, head);
    vox( 0.6, 0.75, 0, 0.2, 0.65, 0.2, C.AL_CHITIN_D, head);
    vox( 0.0, 0.9,  0, 0.22, 0.8,  0.22, C.AL_CHITIN_L, head);

    // 5 Eldritch Eyes
    vox( 0.0,  0.1,  0.62, 0.22, 0.22, 0.1, C.AL_MAG_BRT, head, C.AL_MAG_BRT, 3.0); // Center eye
    vox(-0.35, 0.2,  0.58, 0.18, 0.18, 0.1, C.AL_MAG_NEON, head, C.AL_MAG_NEON, 2.6); // Left upper
    vox( 0.35, 0.2,  0.58, 0.18, 0.18, 0.1, C.AL_MAG_NEON, head, C.AL_MAG_NEON, 2.6); // Right upper
    vox(-0.42,-0.12, 0.55, 0.16, 0.14, 0.1, C.AL_MAG_NEON, head, C.AL_MAG_NEON, 2.4); // Left lower
    vox( 0.42,-0.12, 0.55, 0.16, 0.14, 0.1, C.AL_MAG_NEON, head, C.AL_MAG_NEON, 2.4); // Right lower
    g.add(head);

    // 5. 4 Floating Dark Matter Crystal Shards Orbiting Torso
    const crystals = new THREE.Group();
    crystals.position.set(0, 2.2, 0);
    for (let i = 0; i < 4; i++) {
      const ang = (i / 4) * Math.PI * 2;
      const cMesh = vox(Math.cos(ang) * 1.5, 0, Math.sin(ang) * 1.5, 0.28, 0.6, 0.28, C.AL_VOID_M, crystals, C.AL_CYAN_NEON, 1.8);
      cMesh.rotation.y = Math.PI / 4;
      cMesh.rotation.z = Math.PI / 6;
    }
    g.add(crystals);

    g.scale.setScalar(0.95);
    g.userData.core = core.children[0];
    g.userData.scytheL = scytheL;
    g.userData.scytheR = scytheR;
    g.userData.crystals = crystals;
    return g;
  }

  class EnemyInstance {
    constructor(type, hpMultiplier = 1.0, routeWaypoints = null) {
      this.type = type;
      this.config = ALIEN_CONFIGS[type];
      this.maxHp = Math.round(this.config.baseHp * hpMultiplier);
      this.hp = this.maxHp;
      this.baseSpeed = this.config.speed;
      this.isBoss = this.config.isBoss;

      this.waypoints = (routeWaypoints && routeWaypoints.length > 0) ? routeWaypoints : WAYPOINTS;
      this.distanceTraveled = 0;
      this.waypointIndex = 0;
      this.isDead = false;
      this.reachedSanctum = false;

      // Status timers
      this.stunTimer = 0;
      this.slowTimer = 0;
      this.shredTimer = 0;
      this.hitFlashTimer = 0;
      this.boostTimer = 0;
      this.bossAuraTimer = 0; // Boss ability countdown

      // Elemental Status Timers
      this.zappedTimer = 0;
      this.zappedTickTimer = 0;
      this.zappedDamage = 0;
      this.dirtyTimer = 0;
      this.burnedTimer = 0;
      this.burnedTickTimer = 0;
      this.wetTimer = 0;
      this.tornadoCooldown = 0;
      this.knockbackCooldown = 0; // Cooldown window to prevent rapid chain-knockback pinning

      // Endgame Resistances & Status Immunities
      this.initResistances();
      this.initStatusResistancesAndImmunities();

      // Unique (Shiny) Variant Roll (Starting Wave 5, non-boss only)
      this.isUnique = false;
      this.uniqueTrait = null;
      this.auraTimer = 0;
      this.crownMesh = null;
      this.auraMesh = null;
      if (!this.isBoss && GameState.currentWave >= 5) {
        const rollChance = Math.min(0.25, 0.08 + (GameState.currentWave - 5) * 0.02);
        if (Math.random() < rollChance) {
          this.initUniqueVariant();
        }
      }

      // Spawn 3D Model
      if (type === 'scout') this.model = createAlienScoutModel();
      else if (type === 'trooper') this.model = createVoidTrooperModel();
      else if (type === 'shielder') this.model = createPhaseShielderModel();
      else if (type === 'skitterer') this.model = createSwarmSkittererModel();
      else if (type === 'boss') this.model = createAstralLeviathanBossModel();

      this.position = this.waypoints[0].clone();
      this.model.position.copy(this.position);
      scene.add(this.model);

      // Floating Billboarded Health Bar
      this.createHealthBar();

      // Status Visual Indicator Cube (for Stun)
      this.stunCube = vox(0, (this.isBoss ? 4.2 : 2.2), 0, 0.28, 0.28, 0.28, C.FLOWER_Y, this.model, C.FLOWER_Y, 1.5);
      this.stunCube.visible = false;

      // Clone materials across the ENTIRE model hierarchy (including healthbar and stun cube)
      // so hit flashes NEVER bleach shared cached materials in matCache!
      this.model.traverse(child => {
        if (child.isMesh && child.material) {
          child.material = child.material.clone();
          child.userData.origEmissiveHex = child.material.emissive.getHex();
          child.userData.origEmissiveInt = child.material.emissiveIntensity;
        }
      });

      activeEnemies.push(this);
    }

    createHealthBar() {
      const hbGroup = new THREE.Group();
      const barW = this.isBoss ? 2.0 : 1.1;
      const barH = this.isBoss ? 0.18 : 0.1;
      const barY = this.isBoss ? 4.0 : 1.8;

      // Dark background
      const bgMesh = vox(0, 0, 0, barW, barH, 0.05, 0x111111, hbGroup);

      // Neon fill bar
      const fillColor = this.isBoss ? C.AL_MAG : C.GLOW_GRN;
      const fillMesh = vox(0, 0, 0.03, barW, barH, 0.05, fillColor, hbGroup, fillColor, 1.2);

      hbGroup.position.set(0, barY, 0);
      hbGroup.visible = this.isBoss; // Boss HP always visible
      this.model.add(hbGroup);

      this.healthBarGroup = hbGroup;
      this.healthBarFill = fillMesh;
      this.healthBarWidth = barW;
    }

    initResistances() {
      this.resistances = {
        Physical: 0,
        Magic: 0,
        Thunder: 0,
        Earth: 0,
        Fire: 0,
        Water: 0,
        Explosion: 0
      };

      if (this.isBoss) {
        this.resistances.Physical = 0.20;
        this.resistances.Magic = 0.20;
        this.resistances.Fire = 0.15;
        this.resistances.Thunder = 0.15;
        this.resistances.Water = 0.15;
        this.resistances.Earth = 0.15;
        return;
      }

      // Begins appearing starting at Wave 8 or after 2+ chunks
      const allowResist = (GameState.currentWave >= 8) || (ChunkManager.chunks && ChunkManager.chunks.size >= 2);
      if (!allowResist) return;

      // 60% chance for endgame non-boss enemies to roll a balanced profile
      if (Math.random() > 0.60) return;

      const profiles = [
        { name: 'Obsidian Carapace', Fire: 0.2, Earth: 0.5, Physical: 0.5, Magic: -0.2, Water: -0.3, Thunder: -0.3 },
        { name: 'Frost-Forged', Water: 0.6, Physical: 0.2, Magic: 0.25, Fire: -0.4, Thunder: -0.1 },
        { name: 'Volcanic Chitin', Fire: 0.6, Earth: 0.2, Magic: 0.2, Water: -0.4, Thunder: 0.0 },
        { name: 'Insulated Void', Thunder: 0.6, Magic: 0.45, Earth: -0.4, Physical: -0.1 },
        { name: 'Grounded Bulwark', Earth: 0.6, Physical: 0.3, Magic: -0.2, Thunder: -0.4, Water: 0.0 },
        { name: 'Arcane Dampener', Magic: 0.55, Thunder: 0.25, Physical: -0.25, Fire: -0.25 }
      ];

      if (GameState.currentWave >= 15 && Math.random() < 0.30) {
        profiles.push({ name: 'Blast-Proof Carapace', Explosion: 0.6, Physical: 0.3, Magic: -0.3, Fire: -0.3 });
      }

      const chosen = profiles[Math.floor(Math.random() * profiles.length)];
      this.resistanceProfile = chosen.name;
      for (const [k, v] of Object.entries(chosen)) {
        if (k !== 'name') this.resistances[k] = v;
      }
    }

    initStatusResistancesAndImmunities() {
      // 1. Separate status resistance category (stun & slow)
      this.statusResist = {
        stun: 0, // 0.0 to 0.65
        slow: 0  // 0.0 to 0.65
      };

      // 2. Separate immunities traits
      this.immunities = {
        stun: this.isBoss, // Bosses have innate stun immunity
        slow: false
      };

      this.stunGraceTimer = 0; // Grace timer after recovering from a stun

      const wave = GameState.currentWave;
      if (wave < 11) {
        if (this.isBoss) {
          this.statusResist.slow = 0.35;
        }
        return;
      }

      // Starting at Wave 11: enemies develop increasing resistance to stun and slowness
      // waveFactor grows from 0.0 at Wave 11 to 1.0 at Wave 30
      const waveFactor = Math.min(1.0, (wave - 10) / 20.0);

      // Status resistance threshold: maximum 65% so they can still be stunned or slowed
      const maxStatusThreshold = 0.65;

      if (this.isBoss) {
        this.statusResist.slow = Math.min(maxStatusThreshold, +(0.35 + waveFactor * 0.30).toFixed(2));
      } else {
        // Chance for an enemy to have stun resistance in late waves
        const hasStunResistChance = 0.35 + waveFactor * 0.35;
        if (Math.random() < hasStunResistChance) {
          // Rolls between 0.15 and 0.65 (cuts stun time down by that percentage)
          this.statusResist.stun = Math.min(maxStatusThreshold, +(0.15 + Math.random() * waveFactor * 0.50).toFixed(2));
        }

        // Chance for an enemy to have slow resistance in late waves
        const hasSlowResistChance = 0.35 + waveFactor * 0.35;
        if (Math.random() < hasSlowResistChance) {
          // Rolls between 0.15 and 0.65 (recovers faster / less affected by slow)
          this.statusResist.slow = Math.min(maxStatusThreshold, +(0.15 + Math.random() * waveFactor * 0.50).toFixed(2));
        }

        // Rare Immunity Trait:
        // Starts at ~5% on wave 11, grows slowly with wave up to max 25% (never 100%)
        const immunityPercentage = Math.min(0.25, 0.05 + (wave - 10) * 0.012);
        if (Math.random() < immunityPercentage) {
          if (Math.random() < 0.50) {
            this.immunities.stun = true;
          } else {
            this.immunities.slow = true;
          }
        }
      }
    }

    initUniqueVariant() {
      this.isUnique = true;
      this.model.scale.set(1.32, 1.32, 1.32);

      // Golden Crown Mesh
      const crown = new THREE.Group();
      const headY = (this.type === 'scout' ? 1.5 : (this.type === 'shielder' ? 2.1 : 1.7));
      crown.position.set(0, headY, 0);
      vox(0, 0, 0, 0.45, 0.08, 0.45, 0xFFD700, crown, 0xFFD700, 2.0);
      vox(-0.16, 0.12, -0.16, 0.1, 0.18, 0.1, 0xFFD700, crown, 0xFFD700, 2.5);
      vox( 0.16, 0.12, -0.16, 0.1, 0.18, 0.1, 0xFFD700, crown, 0xFFD700, 2.5);
      vox(-0.16, 0.12,  0.16, 0.1, 0.18, 0.1, 0xFFD700, crown, 0xFFD700, 2.5);
      vox( 0.16, 0.12,  0.16, 0.1, 0.18, 0.1, 0xFFD700, crown, 0xFFD700, 2.5);
      vox(0, 0.18, 0, 0.1, 0.28, 0.1, 0xFFEA00, crown, 0xFFEA00, 3.0);
      this.model.add(crown);
      this.crownMesh = crown;

      // Traits & Auras
      const traits = ['health_boost', 'speed_boost', 'aura_regen', 'aura_speed', 'aura_resist', 'aura_shield', 'aura_cleanse'];
      this.uniqueTrait = traits[Math.floor(Math.random() * traits.length)];

      let auraColor = 0xFFD700;
      let traitTitle = 'SHINY';

      if (this.uniqueTrait === 'health_boost') {
        this.maxHp = Math.round(this.maxHp * 2.0);
        this.hp = this.maxHp;
        traitTitle = 'TITAN';
        auraColor = 0xFF1744;
      } else if (this.uniqueTrait === 'speed_boost') {
        this.baseSpeed *= 1.35;
        traitTitle = 'SWIFT';
        auraColor = 0xFFD700;
      } else if (this.uniqueTrait === 'aura_regen') {
        traitTitle = 'LIFE REGEN';
        auraColor = 0x00E676; // Emerald
      } else if (this.uniqueTrait === 'aura_speed') {
        traitTitle = 'HASTE AURA';
        auraColor = 0xFFD700; // Gold
      } else if (this.uniqueTrait === 'aura_resist') {
        traitTitle = 'WARDING';
        auraColor = 0x00E5FF; // Cyan
      } else if (this.uniqueTrait === 'aura_shield') {
        traitTitle = 'FORTIFIED';
        auraColor = 0xFF1744; // Crimson
      } else if (this.uniqueTrait === 'aura_cleanse') {
        traitTitle = 'CLEANSING';
        auraColor = 0xE040FB; // Violet
      }

      // Voxel Aura Floor Ring
      const ringGeo = new THREE.RingGeometry(0.6, 1.8, 20);
      const ringMat = new THREE.MeshBasicMaterial({
        color: auraColor,
        transparent: true,
        opacity: 0.6,
        side: THREE.DoubleSide
      });
      const ringMesh = new THREE.Mesh(ringGeo, ringMat);
      ringMesh.rotation.x = -Math.PI / 2;
      ringMesh.position.set(0, 0.05, 0);
      this.model.add(ringMesh);
      this.auraMesh = ringMesh;

      GameState.playSound('uniqueSpawn');
      FloatingTextManager.spawnText(this.position, `⭐ UNIQUE ${traitTitle}!`, "status-unique");
    }

    update(dt) {
      if (this.isDead || this.reachedSanctum) return;

      // Update basic status effect timers
      if (this.stunTimer > 0) {
        this.stunTimer -= dt;
        if (this.stunTimer <= 0) {
          this.stunTimer = 0;
          this.stunGraceTimer = 0.40; // Grace timer: enemy cannot be re-stunlocked immediately
        }
      } else if (this.stunGraceTimer > 0) {
        this.stunGraceTimer -= dt;
        if (this.stunGraceTimer <= 0) this.stunGraceTimer = 0;
      }
      if (this.slowTimer > 0) {
        this.slowTimer -= dt;
        if (this.slowTimer <= 0) this.slowTimer = 0;
      }
      if (this.shredTimer > 0) {
        this.shredTimer -= dt;
        if (this.shredTimer <= 0) this.shredTimer = 0;
      }
      if (this.boostTimer > 0) {
        this.boostTimer -= dt;
        if (this.boostTimer <= 0) this.boostTimer = 0;
      }
      if (this.hitFlashTimer > 0) {
        this.hitFlashTimer -= dt;
        if (this.hitFlashTimer <= 0) this.resetHitFlash();
      }
      if (this.knockbackCooldown > 0) {
        this.knockbackCooldown -= dt;
        if (this.knockbackCooldown <= 0) this.knockbackCooldown = 0;
      }

      // Elemental Status Timers & Periodic Ticks
      // 1. Zapped Status: deals Thunder damage every 1.0s and stuns for 0.5s per tick
      if (this.zappedTimer > 0) {
        this.zappedTimer -= dt;
        this.zappedTickTimer -= dt;
        if (this.zappedTickTimer <= 0) {
          this.zappedTickTimer = 1.0;
          const tickDmg = Math.max(5, Math.round((this.zappedDamage || 20) * 0.35));
          this.takeDamage(tickDmg, 'Thunder', false);
          this.applyStatus('stun', 0.5);
          GameState.playSound('electrocuteTick');
          CombatManager.spawnParticleBurst(this.position.clone().add(new THREE.Vector3(0, 0.6, 0)), 4, 0x00E5FF);
        }
      }

      // 2. Dirty Status
      if (this.dirtyTimer > 0) {
        this.dirtyTimer -= dt;
      }

      // 3. Burned Status: deals 2% max HP/s (0.4% if Boss)
      if (this.burnedTimer > 0) {
        this.burnedTimer -= dt;
        this.burnedTickTimer -= dt;
        if (this.burnedTickTimer <= 0) {
          this.burnedTickTimer = 1.0;
          const burnPct = this.isBoss ? 0.004 : 0.02;
          const burnDmg = Math.max(1, Math.round(this.maxHp * burnPct));
          this.takeDamage(burnDmg, 'Fire', false); // Periodic burn NEVER triggers Combustion
          GameState.playSound('burnTick');
          CombatManager.spawnParticleBurst(this.position.clone().add(new THREE.Vector3(0, 0.5, 0)), 4, 0xFF5722);
        }
      }

      // 4. Wet Status
      if (this.wetTimer > 0) {
        this.wetTimer -= dt;
      }

      if (this.tornadoCooldown > 0) {
        this.tornadoCooldown -= dt;
      }

      // Unique Animations & Aura Pulses
      if (this.crownMesh) this.crownMesh.rotation.y += 2.2 * dt;
      if (this.auraMesh) this.auraMesh.rotation.z += 1.6 * dt;

      if (this.isUnique && this.uniqueTrait && this.uniqueTrait.startsWith('aura_')) {
        this.auraTimer = (this.auraTimer || 0) + dt;
        const interval = (this.uniqueTrait === 'aura_cleanse') ? 2.5 : 1.0;
        if (this.auraTimer >= interval) {
          this.auraTimer = 0;
          GameState.playSound('auraPulse');
          activeEnemies.forEach(ally => {
            if (ally !== this && !ally.isBoss && !ally.isDead && this.position.distanceTo(ally.position) <= 3.5) {
              if (this.uniqueTrait === 'aura_regen') {
                const heal = Math.round(ally.maxHp * 0.05);
                ally.hp = Math.min(ally.maxHp, ally.hp + heal);
                FloatingTextManager.spawnText(ally.position, `+${heal} HP`, "status-vuln");
              } else if (this.uniqueTrait === 'aura_speed') {
                ally.boostTimer = 1.2;
              } else if (this.uniqueTrait === 'aura_cleanse') {
                ally.zappedTimer = 0;
                ally.dirtyTimer = 0;
                ally.burnedTimer = 0;
                ally.wetTimer = 0;
                FloatingTextManager.spawnText(ally.position, "CLEANSED!", "status-tornado");
              }
            }
          });
        }
      }

      // Stun visual
      this.stunCube.visible = (this.stunTimer > 0 && !this.isBoss);
      if (this.stunCube.visible) {
        this.stunCube.rotation.y += 8 * dt;
      }

      // Boss Aura Ability: emits speed boost pulse every 4.0s
      if (this.isBoss) {
        this.bossAuraTimer += dt;
        if (this.bossAuraTimer >= 4.0) {
          this.bossAuraTimer = 0;
          CombatManager.triggerBossAura(this.position, 3.5);
          GameState.playSound('bossAura');
        }
      }

      // Calculate effective speed (with Mud Slow synergy: Dirty + Wet = 50% slow!)
      let speedMult = 1.0;
      if (this.slowTimer > 0 && !(this.immunities && this.immunities.slow)) {
        const slowRes = (this.statusResist && this.statusResist.slow) ? Math.min(0.65, this.statusResist.slow) : 0;
        const slowPenalty = 0.30 * (1.0 - slowRes);
        speedMult *= (1.0 - slowPenalty);
      }
      if (this.dirtyTimer > 0) {
        let dirtySlow = (this.wetTimer > 0) ? 0.50 : 0.30;
        if (this.immunities && this.immunities.slow) {
          dirtySlow = 0;
        } else if (this.statusResist && this.statusResist.slow) {
          dirtySlow *= (1.0 - Math.min(0.65, this.statusResist.slow));
        }
        speedMult *= (1.0 - dirtySlow);
      }
      if (this.boostTimer > 0) speedMult *= 1.40;
      if (this.stunTimer > 0 && !this.isBoss && !(this.immunities && this.immunities.stun)) speedMult = 0;

      const currentSpeed = this.baseSpeed * speedMult;

      // Waypoint pathfinding
      if (currentSpeed > 0 && this.waypointIndex < this.waypoints.length - 1) {
        const targetWp = this.waypoints[this.waypointIndex + 1];
        const toTarget = new THREE.Vector3().subVectors(targetWp, this.position);
        toTarget.y = 0;
        const dist = toTarget.length();
        const step = currentSpeed * dt;

        if (dist <= step) {
          this.position.copy(targetWp);
          this.waypointIndex++;
          if (this.waypointIndex >= this.waypoints.length - 1) {
            this.reachSanctum();
            return;
          }
        } else {
          toTarget.normalize();
          this.position.add(toTarget.clone().multiplyScalar(step));
          this.distanceTraveled += step;

          const moveAngle = Math.atan2(toTarget.x, toTarget.z);
          this.model.rotation.y = moveAngle;
        }

        this.model.position.copy(this.position);
      }

      // Billboard health bar to face camera
      if (this.healthBarGroup && this.healthBarGroup.visible) {
        this.healthBarGroup.quaternion.copy(camera.quaternion);
      }

      // Procedural walking/hovering animations
      this.animateModel(dt);
    }

    animateModel(dt) {
      const t = clock.getElapsedTime() * 10;
      if (this.type === 'scout') {
        this.model.position.y = this.position.y + Math.sin(t * 1.2) * 0.15;
      } else if (this.type === 'trooper' && this.model.userData.legL) {
        this.model.userData.legL.rotation.x = Math.sin(t) * 0.45;
        this.model.userData.legR.rotation.x = -Math.sin(t) * 0.45;
      } else if (this.type === 'skitterer' && this.model.userData.legs) {
        this.model.userData.legs[0].rotation.z = Math.sin(t * 2) * 0.3;
        this.model.userData.legs[1].rotation.z = -Math.sin(t * 2) * 0.3;
        this.model.userData.legs[2].rotation.z = -Math.sin(t * 2) * 0.3;
        this.model.userData.legs[3].rotation.z = Math.sin(t * 2) * 0.3;
      } else if (this.type === 'boss') {
        this.model.position.y = this.position.y + Math.sin(t * 0.8) * 0.22;
        if (this.model.userData.scytheL && this.model.userData.scytheR) {
          const scytheAngle = Math.sin(t * 1.4) * 0.16;
          this.model.userData.scytheL.rotation.y = scytheAngle;
          this.model.userData.scytheR.rotation.y = -scytheAngle;
        }
        if (this.model.userData.core) {
          const pulse = 2.0 + Math.sin(t * 2.5) * 1.0;
          this.model.userData.core.material.emissiveIntensity = pulse;
        }
        if (this.model.userData.crystals) {
          this.model.userData.crystals.rotation.y += 1.8 * dt;
        }
      }
    }

    takeDamage(amount, damageType, isDirectFireHit = false) {
      if (this.isDead || this.reachedSanctum) return;

      let finalDmg = amount;

      // Wet Vulnerability: 2x Thunder damage!
      if (damageType === 'Thunder' && this.wetTimer > 0) {
        finalDmg *= 2.0;
        FloatingTextManager.spawnText(this.position, "2x SHOCK!", "status-vuln");
      }

      // Combustion Reaction: Direct Fire attack on a Wet enemy!
      if (isDirectFireHit && this.wetTimer > 0) {
        CombatManager.triggerCombustion(this.position.clone(), finalDmg);
      }

      // Standard Armor Formulas
      if (damageType === 'Physical') {
        if (this.type === 'shielder') {
          const resist = (this.shredTimer > 0) ? 0.25 : 0.50;
          finalDmg *= (1.0 - resist);
        } else {
          if (this.shredTimer > 0) finalDmg *= 1.25;
        }
      } else if (damageType === 'Magic') {
        if (this.type === 'shielder') {
          finalDmg *= 1.25;
        }
      }

      // Endgame Resistances & Weaknesses
      if (this.resistances && this.resistances[damageType]) {
        const res = this.resistances[damageType];
        finalDmg *= (1.0 - res);
        if (res > 0.15 && Math.random() < 0.35) {
          FloatingTextManager.spawnText(this.position, "RESIST", "status-resist");
        } else if (res < -0.15 && Math.random() < 0.35) {
          FloatingTextManager.spawnText(this.position, "WEAKNESS!", "status-vuln");
        }
      }

      // Boss 20% all-damage resist
      if (this.isBoss) {
        finalDmg *= 0.80;
      }

      this.hp -= finalDmg;
      this.triggerHitFlash();

      if (this.healthBarGroup) {
        this.healthBarGroup.visible = true;
        const ratio = Math.max(0.001, this.hp / this.maxHp);
        this.healthBarFill.scale.x = ratio;
        this.healthBarFill.position.x = -this.healthBarWidth * 0.5 * (1 - ratio);
      }

      GameState.playSound('enemyHit');

      // Check 4-Element Combo Reaction (Voxel Tornado)
      this.checkComboReaction();

      if (this.hp <= 0) {
        this.die();
      }
    }

    applyStatus(status, duration) {
      if (status === 'stun') {
        if (this.isBoss || (this.immunities && this.immunities.stun)) {
          if (Math.random() < 0.40) {
            FloatingTextManager.spawnText(this.position, "STUN IMMUNE", "status-resist");
          }
          return;
        }
        if (this.stunGraceTimer > 0) {
          // Stun grace window: enemy recently recovered, cannot be instantly re-stunned
          return;
        }
        const stunRes = (this.statusResist && this.statusResist.stun) ? Math.min(0.65, this.statusResist.stun) : 0;
        const effectiveDuration = duration * (1.0 - stunRes);
        if (effectiveDuration <= 0.05) return;

        if (this.stunTimer <= 0) {
          if (stunRes > 0.15) {
            FloatingTextManager.spawnText(this.position, `STUNNED (-${Math.round(stunRes * 100)}%)`, "status-stun");
          } else {
            FloatingTextManager.spawnText(this.position, "STUNNED!", "status-stun");
          }
        }
        this.stunTimer = Math.max(this.stunTimer, effectiveDuration);
        if (this.stunCube) this.stunCube.visible = true;
      } else if (status === 'slow') {
        if (this.immunities && this.immunities.slow) {
          if (Math.random() < 0.40) {
            FloatingTextManager.spawnText(this.position, "SLOW IMMUNE", "status-resist");
          }
          return;
        }
        const slowRes = (this.statusResist && this.statusResist.slow) ? Math.min(0.65, this.statusResist.slow) : 0;
        const effectiveDuration = duration * (1.0 - slowRes);
        if (effectiveDuration <= 0.05) return;

        if (this.slowTimer <= 0) {
          if (slowRes > 0.15) {
            FloatingTextManager.spawnText(this.position, "SLOW RESIST", "status-resist");
          } else {
            FloatingTextManager.spawnText(this.position, "SLOWED", "status-slow");
          }
        }
        this.slowTimer = Math.max(this.slowTimer, effectiveDuration);
      } else if (status === 'shred') {
        if (this.shredTimer <= 0) {
          FloatingTextManager.spawnText(this.position, "SHREDDED!", "status-shred");
        }
        this.shredTimer = Math.max(this.shredTimer, duration);
      }
    }

    applyElementalStatus(status, duration, damage = 0) {
      if (this.isDead || this.reachedSanctum) return;

      if (status === 'zapped') {
        if (this.zappedTimer <= 0) {
          FloatingTextManager.spawnText(this.position, "⚡ ZAPPED!", "status-zapped");
          this.zappedTickTimer = 1.0;
        }
        this.zappedTimer = 8.0; // Refresh to cap
        this.zappedDamage = damage || this.zappedDamage || 20;
      } else if (status === 'dirty') {
        if (this.dirtyTimer <= 0) {
          FloatingTextManager.spawnText(this.position, "🌿 DIRTY", "status-dirty");
        }
        this.dirtyTimer = 6.0; // Refresh to cap
      } else if (status === 'burned') {
        if (this.burnedTimer <= 0) {
          FloatingTextManager.spawnText(this.position, "🔥 BURNED!", "status-burned");
          this.burnedTickTimer = 1.0;
        }
        this.burnedTimer = 5.0; // Refresh to cap
      } else if (status === 'wet') {
        if (this.wetTimer <= 0) {
          FloatingTextManager.spawnText(this.position, "💧 WET", "status-wet");
        }
        this.wetTimer = 10.0; // Refresh to cap
      }

      this.checkComboReaction();
    }

    knockback(dist = 0.6) {
      if (this.isBoss) return;
      if (this.knockbackCooldown > 0) return; // In cooldown: cannot be repeatedly knocked back

      // Set cooldown window (2.2s) before enemy can be knocked back again
      this.knockbackCooldown = 2.2;

      // Earth resistance slightly dampens knockback distance if applicable
      const earthRes = (this.resistances && this.resistances.Earth) ? Math.max(0, this.resistances.Earth) : 0;
      const effectiveDist = dist * Math.max(0.35, 1.0 - earthRes);

      this.distanceTraveled = Math.max(0, this.distanceTraveled - effectiveDist);
      let remaining = this.distanceTraveled;
      for (let i = 0; i < this.waypoints.length - 1; i++) {
        const segLen = this.waypoints[i].distanceTo(this.waypoints[i + 1]);
        if (remaining <= segLen) {
          this.waypointIndex = i;
          const t = segLen > 0.001 ? remaining / segLen : 0;
          this.position.lerpVectors(this.waypoints[i], this.waypoints[i + 1], t);
          this.model.position.copy(this.position);
          break;
        }
        remaining -= segLen;
      }

      GameState.playSound('knockbackImpact');
      CombatManager.spawnParticleBurst(this.position.clone().add(new THREE.Vector3(0, 0.35, 0)), 5, 0x8D6E63);
    }

    checkComboReaction() {
      if (this.tornadoCooldown > 0) return;
      if (this.wetTimer > 0 && this.zappedTimer > 0 && this.burnedTimer > 0 && this.dirtyTimer > 0) {
        this.tornadoCooldown = 3.0;
        CombatManager.spawnVoxelTornado(this.position.clone());
      }
    }

    triggerHitFlash() {
      this.hitFlashTimer = 0.1;
      this.model.traverse(child => {
        if (child.isMesh && child.material && child !== this.stunCube && child.parent !== this.healthBarGroup && child !== this.auraMesh) {
          child.material.emissive.setHex(0xFFFFFF);
          child.material.emissiveIntensity = 1.6;
        }
      });
    }

    resetHitFlash() {
      this.model.traverse(child => {
        if (child.isMesh && child.material && child.userData.origEmissiveHex !== undefined) {
          child.material.emissive.setHex(child.userData.origEmissiveHex);
          child.material.emissiveIntensity = child.userData.origEmissiveInt;
        }
      });
    }

    reachSanctum() {
      this.reachedSanctum = true;
      GameState.damageSanctum(this.config.penalty);
      this.destroy();
    }

    die() {
      this.isDead = true;
      GameState.addShards(this.config.shards);
      GameState.totalKills = (GameState.totalKills || 0) + 1;
      GameState.totalShardsEarned = (GameState.totalShardsEarned || 0) + this.config.shards;
      FloatingTextManager.spawnText(this.position, `+${this.config.shards}💎`, "shard-reward");

      // Bosses exclusively drop 1 Astral Essence!
      if (this.isBoss) {
        GameState.addEssence(1);
        FloatingTextManager.spawnText(this.position.clone().add(new THREE.Vector3(0, 1.0, 0)), "+1 🔮 ESSENCE!", "essence-reward");
      }

      CombatManager.spawnDeathParticles(this.position.clone(), this.type);
      GameState.playSound('enemyDeath');
      this.destroy();
      WaveManager.checkWaveCompletion();
    }

    destroy() {
      scene.remove(this.model);
      const idx = activeEnemies.indexOf(this);
      if (idx !== -1) activeEnemies.splice(idx, 1);
    }
  }

  // ========================================================
  // COMBAT MANAGER (Projectiles, AoE, Chains, Particles)
  // ========================================================
  const CombatManager = {
    // Parabolic Boulder Launch (Stone Golem)
    launchBoulder: function (startPos, targetPos, damage, aoeRadius, element = null, dmgType = 'Physical') {
      let bColor = C.SG_D;
      let emColor = null;
      if (element === 'thunder') { bColor = 0x00E5FF; emColor = 0x00E5FF; }
      else if (element === 'earth') { bColor = 0x5D4037; emColor = 0x76FF03; }
      else if (element === 'fire') { bColor = 0xD84315; emColor = 0xFF5722; }
      else if (element === 'water') { bColor = 0x1976D2; emColor = 0x40C4FF; }

      const bMesh = vox(0, 0, 0, 0.45, 0.45, 0.45, bColor, scene, emColor, emColor ? 2.0 : 0);
      bMesh.position.copy(startPos);

      activeProjectiles.push({
        type: 'boulder',
        mesh: bMesh,
        startPos: startPos,
        targetPos: targetPos,
        damage: damage,
        aoeRadius: aoeRadius,
        element: element,
        dmgType: dmgType,
        flightTime: 0.5,
        elapsed: 0,
        update: function (dt) {
          this.elapsed += dt;
          const t = Math.min(1.0, this.elapsed / this.flightTime);
          this.mesh.position.lerpVectors(this.startPos, this.targetPos, t);
          this.mesh.position.y += Math.sin(t * Math.PI) * 2.5;

          this.mesh.rotation.x += 12 * dt;
          this.mesh.rotation.z += 8 * dt;

          if (t >= 1.0) {
            // Impact!
            scene.remove(this.mesh);
            const burstCol = this.element === 'thunder' ? 0x00E5FF : (this.element === 'earth' ? 0x76FF03 : (this.element === 'fire' ? 0xFF5722 : (this.element === 'water' ? 0x2979FF : C.SAND_D)));
            CombatManager.spawnParticleBurst(this.targetPos, 8, burstCol);

            // AoE Damage & Elemental Application
            activeEnemies.forEach(e => {
              if (e.position.distanceTo(this.targetPos) <= this.aoeRadius) {
                e.takeDamage(this.damage, this.dmgType, this.element === 'fire');
                if (this.element) {
                  const status = this.element === 'thunder' ? 'zapped' : (this.element === 'earth' ? 'dirty' : (this.element === 'fire' ? 'burned' : 'wet'));
                  const dur = this.element === 'thunder' ? 8.0 : (this.element === 'earth' ? 6.0 : (this.element === 'fire' ? 5.0 : 10.0));
                  e.applyElementalStatus(status, dur, this.damage);
                  if (this.element === 'earth') e.knockback(0.6);
                }
              }
            });
            GameState.playSound('stoneImpact');
            return true;
          }
          return false;
        }
      });
    },

    // High-Velocity Slug (Oak Golem)
    fireSlug: function (startPos, targetEnemy, damage, isCrit = false, element = null, dmgType = 'Physical', splashRadius = 0) {
      let sColor = isCrit ? 0xFF2A85 : C.OG_WD_DK;
      let emColor = isCrit ? 0xFF2A85 : C.OG_MTL;
      if (element === 'thunder') { sColor = 0x00E5FF; emColor = 0x00E5FF; }
      else if (element === 'earth') { sColor = 0x5D4037; emColor = 0x76FF03; }
      else if (element === 'fire') { sColor = 0xD84315; emColor = 0xFF5722; }
      else if (element === 'water') { sColor = 0x1976D2; emColor = 0x40C4FF; }

      const sMesh = vox(0, 0, 0, 0.22, 0.22, 0.45, sColor, scene, emColor, 1.8);
      sMesh.position.copy(startPos);

      activeProjectiles.push({
        type: 'slug',
        mesh: sMesh,
        target: targetEnemy,
        lastKnownPos: targetEnemy.position.clone().add(new THREE.Vector3(0, 0.6, 0)),
        damage: damage,
        isCrit: isCrit,
        element: element,
        dmgType: dmgType,
        splashRadius: splashRadius,
        speed: 16.0,
        update: function (dt) {
          if (!this.target.isDead && !this.target.reachedSanctum) {
            this.lastKnownPos.copy(this.target.position).add(new THREE.Vector3(0, 0.6, 0));
          }

          const dir = new THREE.Vector3().subVectors(this.lastKnownPos, this.mesh.position);
          const dist = dir.length();
          const step = this.speed * dt;

          if (dist <= step) {
            scene.remove(this.mesh);

            if (this.splashRadius > 0) {
              // Water AoE Splash!
              activeEnemies.forEach(e => {
                if (e.position.distanceTo(this.lastKnownPos) <= this.splashRadius) {
                  e.takeDamage(this.damage, this.dmgType, this.element === 'fire');
                  if (this.element) {
                    const status = this.element === 'thunder' ? 'zapped' : (this.element === 'earth' ? 'dirty' : (this.element === 'fire' ? 'burned' : 'wet'));
                    const dur = this.element === 'thunder' ? 8.0 : (this.element === 'earth' ? 6.0 : (this.element === 'fire' ? 5.0 : 10.0));
                    e.applyElementalStatus(status, dur, this.damage);
                    if (this.element === 'earth') e.knockback(0.6);
                  }
                }
              });
            } else if (!this.target.isDead) {
              this.target.takeDamage(this.damage, this.dmgType, this.element === 'fire');
              if (this.element) {
                const status = this.element === 'thunder' ? 'zapped' : (this.element === 'earth' ? 'dirty' : (this.element === 'fire' ? 'burned' : 'wet'));
                const dur = this.element === 'thunder' ? 8.0 : (this.element === 'earth' ? 6.0 : (this.element === 'fire' ? 5.0 : 10.0));
                this.target.applyElementalStatus(status, dur, this.damage);
                if (this.element === 'earth') this.target.knockback(0.6);
              }
              if (this.isCrit) {
                FloatingTextManager.spawnText(this.lastKnownPos, "CRIT! 2x", "crit-hit");
              }
            }

            const pCol = this.isCrit ? 0xFF2A85 : (this.element === 'thunder' ? 0x00E5FF : (this.element === 'water' ? 0x2979FF : (this.element === 'fire' ? 0xFF5722 : C.OG_MTL)));
            CombatManager.spawnParticleBurst(this.lastKnownPos, 4, pCol);
            return true;
          }

          dir.normalize();
          this.mesh.position.add(dir.multiplyScalar(step));
          this.mesh.lookAt(this.lastKnownPos);
          return false;
        }
      });
    },

    // Muzzle Flash Effect
    spawnMuzzleFlash: function (pos) {
      const flash = vox(pos.x, pos.y, pos.z, 0.35, 0.35, 0.35, 0xFFE082, scene, 0xFFE082, 3.0);
      activeParticles.push({
        mesh: flash,
        life: 0.08,
        update: function (dt) {
          this.life -= dt;
          if (this.life <= 0) {
            scene.remove(this.mesh);
            return true;
          }
          return false;
        }
      });
    },

    // Seismic Ground Slam (Brick Golem)
    triggerGroundSlam: function (centerPos, maxRadius, damage, stunDuration = 0.8, element = null, dmgType = 'Physical') {
      let ringColor = C.GLOW_GRN;
      if (element === 'thunder') ringColor = 0x00E5FF;
      else if (element === 'earth') ringColor = 0x76FF03;
      else if (element === 'fire') ringColor = 0xFF5722;
      else if (element === 'water') ringColor = 0x2979FF;

      const ringGeo = new THREE.RingGeometry(0.1, 0.2, 32);
      const ringMat = new THREE.MeshBasicMaterial({
        color: ringColor,
        transparent: true,
        opacity: 0.85,
        side: THREE.DoubleSide
      });
      const slamMesh = new THREE.Mesh(ringGeo, ringMat);
      slamMesh.rotation.x = -Math.PI / 2;
      slamMesh.position.set(centerPos.x, centerPos.y + 0.04, centerPos.z);
      scene.add(slamMesh);

      activeSlamRings.push({
        mesh: slamMesh,
        radius: 0.1,
        maxRadius: maxRadius,
        duration: 0.3,
        elapsed: 0,
        element: element,
        dmgType: dmgType,
        hitSet: new Set(),
        update: function (dt) {
          this.elapsed += dt;
          const t = Math.min(1.0, this.elapsed / this.duration);
          this.radius = THREE.MathUtils.lerp(0.1, this.maxRadius, t);
          this.mesh.scale.set(this.radius, this.radius, 1);
          this.mesh.material.opacity = 0.85 * (1.0 - t);

          activeEnemies.forEach(e => {
            if (!this.hitSet.has(e) && centerPos.distanceTo(e.position) <= this.radius) {
              this.hitSet.add(e);
              e.takeDamage(damage, this.dmgType, this.element === 'fire');
              e.applyStatus('stun', stunDuration);
              e.applyStatus('shred', 3.0);
              if (this.element) {
                const status = this.element === 'thunder' ? 'zapped' : (this.element === 'earth' ? 'dirty' : (this.element === 'fire' ? 'burned' : 'wet'));
                const dur = this.element === 'thunder' ? 8.0 : (this.element === 'earth' ? 6.0 : (this.element === 'fire' ? 5.0 : 10.0));
                e.applyElementalStatus(status, dur, damage);
                if (this.element === 'earth') e.knockback(0.6);
              }
            }
          });

          if (t >= 1.0) {
            scene.remove(this.mesh);
            return true;
          }
          return false;
        }
      });
    },

    // Arcane Chain Beam (Diorite Golem)
    fireChainBeam: function (originPos, primaryTarget, baseDamage, maxJumps = 2, slowDuration = 2.5, element = null, dmgType = 'Magic') {
      const chainTargets = [primaryTarget];
      let currentOrigin = primaryTarget.position;

      for (let jump = 0; jump < maxJumps; jump++) {
        let bestNext = null;
        let bestDist = 2.5;
        for (let i = 0; i < activeEnemies.length; i++) {
          const e = activeEnemies[i];
          if (chainTargets.includes(e) || e.isDead || e.reachedSanctum) continue;
          const d = currentOrigin.distanceTo(e.position);
          if (d <= bestDist) {
            bestDist = d;
            bestNext = e;
          }
        }
        if (bestNext) {
          chainTargets.push(bestNext);
          currentOrigin = bestNext.position;
        } else {
          break;
        }
      }

      let startPoint = originPos.clone();
      let dmg = baseDamage;

      let beamColor = C.DG_GLD;
      if (element === 'thunder') beamColor = 0x00E5FF;
      else if (element === 'earth') beamColor = 0x76FF03;
      else if (element === 'fire') beamColor = 0xFF5722;
      else if (element === 'water') beamColor = 0x2979FF;

      chainTargets.forEach((target, idx) => {
        const endPoint = target.position.clone().add(new THREE.Vector3(0, 0.6, 0));
        CombatManager.createBeamSegment(startPoint, endPoint, beamColor);

        target.takeDamage(dmg, dmgType, element === 'fire');
        target.applyStatus('slow', slowDuration);
        if (element) {
          const status = element === 'thunder' ? 'zapped' : (element === 'earth' ? 'dirty' : (element === 'fire' ? 'burned' : 'wet'));
          const dur = element === 'thunder' ? 8.0 : (element === 'earth' ? 6.0 : (element === 'fire' ? 5.0 : 10.0));
          target.applyElementalStatus(status, dur, dmg);
          if (element === 'earth') target.knockback(0.6);
        }

        startPoint = endPoint;
        dmg *= 0.75;
      });
    },

    createBeamSegment: function (start, end, colorHex = C.DG_GLD) {
      const dir = new THREE.Vector3().subVectors(end, start);
      const length = dir.length();
      const beamMesh = vox(0, 0, 0, 0.14, 0.14, length, colorHex, scene, colorHex, 3.0, 0.95);

      beamMesh.position.copy(start).add(dir.clone().multiplyScalar(0.5));
      beamMesh.lookAt(end);

      activeBeams.push({
        mesh: beamMesh,
        life: 0.15,
        update: function (dt) {
          this.life -= dt;
          this.mesh.material.opacity = Math.max(0, this.life / 0.15);
          if (this.life <= 0) {
            scene.remove(this.mesh);
            return true;
          }
          return false;
        }
      });
    },

    // Combustion Elemental Reaction (Direct Fire on Wet enemy)
    triggerCombustion: function (pos, damage) {
      const blastDmg = Math.round(damage * 1.3);
      FloatingTextManager.spawnText(pos, "🔥💥 COMBUSTION!", "status-combustion");
      GameState.playSound('combustionExplode');
      this.spawnParticleBurst(pos.clone().add(new THREE.Vector3(0, 0.6, 0)), 24, 0xFF5722);
      this.spawnParticleBurst(pos.clone().add(new THREE.Vector3(0, 0.6, 0)), 16, 0x2979FF);
      this.spawnParticleBurst(pos.clone().add(new THREE.Vector3(0, 0.6, 0)), 12, 0xFFEB3B);

      activeEnemies.forEach(e => {
        if (e.position.distanceTo(pos) <= 2.2) {
          e.takeDamage(blastDmg, 'Explosion', false);
        }
      });
    },

    // 4-Element Combo Reaction (Voxel Tornado)
    spawnVoxelTornado: function (centerPos) {
      const tGroup = new THREE.Group();
      tGroup.position.copy(centerPos);

      const colors = [0x00E5FF, 0x76FF03, 0xFF5722, 0x2979FF];
      const tiers = [
        { y: 0.3, r: 0.5, size: 0.2 },
        { y: 0.9, r: 0.85, size: 0.24 },
        { y: 1.6, r: 1.25, size: 0.28 },
        { y: 2.3, r: 1.6, size: 0.32 }
      ];
      tiers.forEach(tier => {
        for (let i = 0; i < 4; i++) {
          const ang = (i / 4) * Math.PI * 2;
          const col = colors[i % colors.length];
          vox(Math.cos(ang) * tier.r, tier.y, Math.sin(ang) * tier.r, tier.size, tier.size, tier.size, col, tGroup, col, 2.5);
        }
      });
      scene.add(tGroup);

      FloatingTextManager.spawnText(centerPos, "🌪️ VOXEL TORNADO!", "status-tornado");
      GameState.playSound('tornadoRoar');

      const tickTimes = [0.0, 0.3, 0.6, 0.9, 1.2, 1.5];
      let nextTickIdx = 0;

      activeTornadoes.push({
        mesh: tGroup,
        center: centerPos.clone(),
        elapsed: 0,
        duration: 1.5,
        update: function (dt) {
          this.elapsed += dt;
          this.mesh.rotation.y += 16.0 * dt;

          while (nextTickIdx < tickTimes.length && this.elapsed >= tickTimes[nextTickIdx]) {
            nextTickIdx++;
            activeEnemies.forEach(e => {
              if (e.position.distanceTo(this.center) <= 3.0) {
                e.takeDamage(12, 'Physical', false);
                e.takeDamage(12, 'Thunder', false);
                e.takeDamage(12, 'Earth', false);
                e.takeDamage(12, 'Fire', false);
                e.takeDamage(12, 'Water', false);
              }
            });
            CombatManager.spawnParticleBurst(this.center.clone().add(new THREE.Vector3(0, 1.0, 0)), 6, colors[nextTickIdx % colors.length]);
          }

          if (this.elapsed >= this.duration) {
            scene.remove(this.mesh);
            return true;
          }
          return false;
        }
      });
    },

    // Boss Magenta Pulse Wave
    triggerBossAura: function (centerPos, radius) {
      const ringGeo = new THREE.RingGeometry(0.1, 0.3, 32);
      const ringMat = new THREE.MeshBasicMaterial({
        color: C.AL_MAG,
        transparent: true,
        opacity: 0.9,
        side: THREE.DoubleSide
      });
      const pulseMesh = new THREE.Mesh(ringGeo, ringMat);
      pulseMesh.rotation.x = -Math.PI / 2;
      pulseMesh.position.set(centerPos.x, centerPos.y + 0.1, centerPos.z);
      scene.add(pulseMesh);

      // Boost speed of all nearby alien units by +40% for 3.0s
      activeEnemies.forEach(e => {
        if (!e.isBoss && centerPos.distanceTo(e.position) <= radius) {
          e.boostTimer = 3.0;
        }
      });

      activeSlamRings.push({
        mesh: pulseMesh,
        radius: 0.1,
        maxRadius: radius,
        duration: 0.45,
        elapsed: 0,
        update: function (dt) {
          this.elapsed += dt;
          const t = Math.min(1.0, this.elapsed / this.duration);
          this.radius = THREE.MathUtils.lerp(0.1, this.maxRadius, t);
          this.mesh.scale.set(this.radius, this.radius, 1);
          this.mesh.material.opacity = 0.9 * (1.0 - t);
          if (t >= 1.0) {
            scene.remove(this.mesh);
            return true;
          }
          return false;
        }
      });
    },

    // Death Voxel Burst Particles
    spawnDeathParticles: function (pos, enemyType) {
      if (enemyType === 'boss') {
        this.spawnParticleBurst(pos.clone().add(new THREE.Vector3(0, 1.5, 0)), 32, C.AL_MAG_NEON);
        this.spawnParticleBurst(pos.clone().add(new THREE.Vector3(0, 1.5, 0)), 18, C.AL_CYAN_NEON);
      } else if (enemyType === 'skitterer') {
        this.spawnParticleBurst(pos.clone().add(new THREE.Vector3(0, 0.3, 0)), 14, C.AL_ACID);
        this.spawnParticleBurst(pos.clone().add(new THREE.Vector3(0, 0.3, 0)), 8, C.AL_CHITIN_D);
      } else if (enemyType === 'shielder') {
        this.spawnParticleBurst(pos.clone().add(new THREE.Vector3(0, 0.8, 0)), 16, C.AL_CYAN_NEON);
        this.spawnParticleBurst(pos.clone().add(new THREE.Vector3(0, 0.8, 0)), 10, C.AL_GOLD_ARM);
      } else {
        const col = (enemyType === 'trooper') ? C.AL_MAG_NEON : C.AL_CYAN_NEON;
        this.spawnParticleBurst(pos.clone().add(new THREE.Vector3(0, 0.5, 0)), 14, col);
        this.spawnParticleBurst(pos.clone().add(new THREE.Vector3(0, 0.5, 0)), 8, C.AL_CHITIN_D);
      }
    },

    spawnParticleBurst: function (pos, count, colorHex) {
      for (let i = 0; i < count; i++) {
        const size = 0.14 + Math.random() * 0.08;
        const pMesh = vox(pos.x, pos.y, pos.z, size, size, size, colorHex, scene);

        const angle = Math.random() * Math.PI * 2;
        const hSpeed = 1.0 + Math.random() * 2.5;

        activeParticles.push({
          mesh: pMesh,
          vx: Math.cos(angle) * hSpeed,
          vy: 2.5 + Math.random() * 3.5,
          vz: Math.sin(angle) * hSpeed,
          life: 0.6,
          maxLife: 0.6,
          bounced: false,
          update: function (dt) {
            this.life -= dt;
            this.vy -= 15.0 * dt; // gravity

            this.mesh.position.x += this.vx * dt;
            this.mesh.position.y += this.vy * dt;
            this.mesh.position.z += this.vz * dt;

            // Ground bounce
            if (this.mesh.position.y <= 0.88 && !this.bounced) {
              this.mesh.position.y = 0.88;
              this.vy = -this.vy * 0.4;
              this.vx *= 0.6;
              this.vz *= 0.6;
              this.bounced = true;
            }

            const scale = Math.max(0.001, this.life / this.maxLife);
            this.mesh.scale.set(scale, scale, scale);

            if (this.life <= 0) {
              scene.remove(this.mesh);
              return true;
            }
            return false;
          }
        });
      }
    },

    spawnAscensionSpiral: function (pos, count = 36) {
      for (let i = 0; i < count; i++) {
        const size = 0.16 + Math.random() * 0.08;
        const col = (i % 2 === 0) ? 0xFFD700 : 0x39FF14;
        const pMesh = vox(pos.x, pos.y, pos.z, size, size, size, col, scene, col, 2.4);

        const angle = (i / count) * Math.PI * 4;
        const radius = 0.35 + (i / count) * 0.55;

        activeParticles.push({
          mesh: pMesh,
          angle: angle,
          radius: radius,
          vy: 2.5 + (i / count) * 2.8,
          life: 0.95,
          maxLife: 0.95,
          center: pos.clone(),
          update: function (dt) {
            this.life -= dt;
            this.angle += 6.5 * dt;
            this.mesh.position.x = this.center.x + Math.cos(this.angle) * this.radius;
            this.mesh.position.z = this.center.z + Math.sin(this.angle) * this.radius;
            this.mesh.position.y += this.vy * dt;

            const scale = Math.max(0.001, this.life / this.maxLife);
            this.mesh.scale.set(scale, scale, scale);

            if (this.life <= 0) {
              scene.remove(this.mesh);
              return true;
            }
            return false;
          }
        });
      }
    }
  };

  // ========================================================
  // PROCEDURAL MODULAR CHUNK SYSTEM (Building Blocks)
  // ========================================================
  const ChunkManager = {
    chunks: new Map(), // key: 'cx,cz' => chunk object
    activePortals: [],
    arrowObjects: [], // 3D interactive procedural wedge arrows
    bannerObjects: [], // legacy alias
    nextPedestalId: 10,
    animatingVoxels: [], // rising voxel wave animation queue

    init: function () {
      this.chunks.forEach(chunk => {
        if (chunk.cx !== 0 || chunk.cz !== 0) {
          if (chunk.group && chunk.group.parent) chunk.group.parent.remove(chunk.group);
        }
      });
      carvedConnectorMeshes.forEach(mesh => {
        if (mesh && mesh.parent) mesh.parent.remove(mesh);
      });
      carvedConnectorMeshes = [];

      this.chunks.clear();
      this.activePortals = [];
      this.animatingVoxels = [];
      this.clear3DArrows();

      // Register base chunk (0, 0)
      const baseChunk = {
        cx: 0,
        cz: 0,
        id: '0,0',
        portalPos: WAYPOINTS.length > 0 ? WAYPOINTS[0] : new THREE.Vector3(14, 0.85, 2),
        portalGroup: startingPortalGroup,
        waypoints: WAYPOINTS,
        fullWaypoints: WAYPOINTS,
        pedestals: pedestals.slice(0, 10),
      };
      this.chunks.set('0,0', baseChunk);

      this.activePortals = [
        {
          id: 'portal_0_0',
          cx: 0,
          cz: 0,
          pos: baseChunk.portalPos,
          waypoints: WAYPOINTS,
          portalGroup: startingPortalGroup
        }
      ];
    },

    getAvailableExpansions: function () {
      const directions = [
        { dir: 'north', dx: 0, dz: -1, name: 'North Sector', icon: '⬆️' },
        { dir: 'east',  dx: 1, dz: 0,  name: 'East Sector',  icon: '➡️' },
        { dir: 'south', dx: 0, dz: 1,  name: 'South Sector', icon: '⬇️' },
        { dir: 'west',  dx: -1, dz: 0, name: 'West Sector',  icon: '⬅️' }
      ];

      const available = [];
      const edgeSet = new Set();

      this.chunks.forEach(chunk => {
        directions.forEach(d => {
          const targetCx = chunk.cx + d.dx;
          const targetCz = chunk.cz + d.dz;
          const targetKey = `${targetCx},${targetCz}`;

          // Smart Adjacency Filtering:
          // ONLY spawn arrows on exposed outer edges facing undiscovered space!
          // Interior borders shared between two already-revealed chunks NEVER spawn an arrow.
          if (!this.chunks.has(targetKey)) {
            const edgeKey = `${chunk.cx},${chunk.cz}->${d.dir}`;
            if (!edgeSet.has(edgeKey)) {
              edgeSet.add(edgeKey);
              available.push({
                targetCx,
                targetCz,
                fromCx: chunk.cx,
                fromCz: chunk.cz,
                dir: d.dir,
                name: `${d.name} [${targetCx}, ${targetCz}]`,
                icon: d.icon,
                desc: `Pristine desert sector with procedural path & 6+ new pedestals.`
              });
            }
          }
        });
      });

      return available;
    },

    showExpansionPrompt: function () {
      const available = this.getAvailableExpansions();
      if (available.length === 0) return;

      GameState.awaitingExpansion = true;
      GameState.playSound('expansionUnlock');

      // Subtle, non-intrusive pixel HUD prompt at top of overworld
      const promptBar = document.getElementById('expansion-prompt-bar');
      if (promptBar) promptBar.classList.remove('hidden');

      // Update action button on top HUD
      updateHud();

      // Spawn procedural 3D Voxel Wedge Arrows along exposed outer edges
      this.spawn3DArrows(available);

      // Smoothly tween/zoom out camera to comfortably frame all active arrows
      this.frameCameraForExpansion();
    },

    selectExpansion: function (exp) {
      if (!exp) return;
      this.clear3DArrows();

      const promptBar = document.getElementById('expansion-prompt-bar');
      if (promptBar) promptBar.classList.add('hidden');

      GameState.awaitingExpansion = false;

      // Generate & connect the new chunk
      this.expandChunk(exp.targetCx, exp.targetCz, exp.fromCx, exp.fromCz, exp.dir);

      // Restore wave-ready gameplay
      updateHud();
    },

    expandChunk: function (targetCx, targetCz, fromCx, fromCz, dir) {
      this.clear3DArrows();
      const promptBar = document.getElementById('expansion-prompt-bar');
      if (promptBar) promptBar.classList.add('hidden');
      GameState.awaitingExpansion = false;

      // Generate the new procedural chunk
      const chunk = this.generateChunk(targetCx, targetCz, fromCx, fromCz, dir);
      this.chunks.set(`${targetCx},${targetCz}`, chunk);

      // Recalculate multi-portals based on total chunks count
      this.updateActivePortals();

      // Trigger wave rise rumble audio & particles
      GameState.playSound('stoneRumble');

      // Smooth camera pan towards center of the new territory
      const targetMidX = targetCx * 16 + 8;
      const targetMidZ = targetCz * 16 + 8;
      targetCameraPos.set(
        (targetMidX + targetCameraPos.x) * 0.5,
        1.5,
        (targetMidZ + targetCameraPos.z) * 0.5
      );
      targetZoom = 11.5;

      FloatingTextManager.spawnText(
        new THREE.Vector3(targetMidX, 3.0, targetMidZ),
        `SECTOR [${targetCx},${targetCz}] REVEALED!`,
        'shard-reward'
      );

      GameState.totalWaves += 10;
      GameState.realmExpanded = true;
      updateHud();
    },

    updateActivePortals: function () {
      const count = this.chunks.size;
      // 1-2 chunks => 1 portal
      // 3-4 chunks => 2 portals in different areas
      // 5+ chunks  => 3 portals
      let desiredCount = 1;
      if (count >= 5) desiredCount = 3;
      else if (count >= 3) desiredCount = 2;

      const allPortals = [];
      this.chunks.forEach(chunk => {
        if (chunk.portalPos && chunk.fullWaypoints) {
          allPortals.push({
            id: `portal_${chunk.cx}_${chunk.cz}`,
            cx: chunk.cx,
            cz: chunk.cz,
            pos: chunk.portalPos,
            waypoints: chunk.fullWaypoints,
            portalGroup: chunk.portalGroup
          });
        }
      });

      // Sort portals by distance to Sanctum (furthest outer portals prioritize active duty)
      const sanctumPos = new THREE.Vector3(4.0, 0.85, 4.0);
      allPortals.sort((a, b) => b.pos.distanceTo(sanctumPos) - a.pos.distanceTo(sanctumPos));

      this.activePortals = allPortals.slice(0, desiredCount);
      console.log(`Active invasion portals: ${this.activePortals.length} across ${count} sectors`);
    },

    checkAndDestroyMidwayPortals: function (newPathWaypoints, newPortalPos, fromCx, fromCz) {
      if (!newPathWaypoints || newPathWaypoints.length < 2) return 0;

      // Waypoint 0 is the new leaf portal. Waypoints 1..end trace the extended route back to the Sanctum.
      const pathWaypoints = newPathWaypoints.slice(1);
      const portalsToDestroy = [];

      this.chunks.forEach(chunk => {
        if (!chunk.portalPos || !chunk.portalGroup) return;

        // Skip if this is the new portal itself
        if (Math.hypot(chunk.portalPos.x - newPortalPos.x, chunk.portalPos.z - newPortalPos.z) < 0.5) {
          return;
        }

        // Check if chunk.portalPos is midway along the new route
        let minDistance = Infinity;
        for (let i = 0; i < pathWaypoints.length; i++) {
          const wp = pathWaypoints[i];
          const dist = Math.hypot(chunk.portalPos.x - wp.x, chunk.portalPos.z - wp.z);
          if (dist < minDistance) minDistance = dist;
          if (dist <= 1.45) break;
        }

        // Portals along the route (within 2.5 tiles) OR portal on the parent chunk being extended outwards
        const isFromChunkPortal = (fromCx !== undefined && fromCz !== undefined && chunk.cx === fromCx && chunk.cz === fromCz);

        if (minDistance <= 2.5 || isFromChunkPortal) {
          portalsToDestroy.push({ chunk, distance: minDistance });
        }
      });

      portalsToDestroy.forEach(({ chunk, distance }) => {
        console.log(`[ChunkManager] Collapsing midway portal on chunk [${chunk.cx},${chunk.cz}] at (${chunk.portalPos.x.toFixed(1)}, ${chunk.portalPos.z.toFixed(1)}) - dist to path: ${distance.toFixed(2)}`);

        const pPos = chunk.portalPos.clone();

        // 1. Resonant void collapse audio effect
        GameState.playSound('portalCollapse');

        // 2. Cosmic void collapse particle bursts
        CombatManager.spawnParticleBurst(pPos.clone().add(new THREE.Vector3(0, 1.2, 0)), 28, 0xFF1447);
        CombatManager.spawnParticleBurst(pPos.clone().add(new THREE.Vector3(0, 0.5, 0)), 16, C.STN_D);
        CombatManager.spawnParticleBurst(pPos.clone().add(new THREE.Vector3(0, 2.0, 0)), 14, 0x9B26B6);

        // 3. Floating notification text
        FloatingTextManager.spawnText(
          pPos.clone().add(new THREE.Vector3(0, 2.8, 0)),
          '🌀 MIDWAY PORTAL COLLAPSED!',
          'crit-dmg'
        );

        // 4. Remove runes from animation registry
        if (chunk.portalGroup) {
          portalRunes = portalRunes.filter(pr => {
            let cur = pr.parent;
            while (cur) {
              if (cur === chunk.portalGroup) return false;
              cur = cur.parent;
            }
            return true;
          });

          // Remove 3D group from parent/scene
          if (chunk.portalGroup.parent) {
            chunk.portalGroup.parent.remove(chunk.portalGroup);
          }
        }

        // 5. Clear logical references so it is no longer counted as an active portal
        chunk.portalPos = null;
        chunk.portalGroup = null;
      });

      return portalsToDestroy.length;
    },

    generateChunk: function (cx, cz, fromCx, fromCz, dir) {
      const chunkGroup = new THREE.Group();
      const originX = cx * 16;
      const originZ = cz * 16;

      // 1. Bedrock Plinth
      for (let lx = 0; lx < 16; lx++) {
        for (let lz = 0; lz < 16; lz++) {
          const wx = originX + lx;
          const wz = originZ + lz;
          vox(wx, -0.5, wz, 1, 1, 1, C.SAND_X, chunkGroup);
          vox(wx, -1.5, wz, 1, 1, 1, C.BED_1,  chunkGroup);
          vox(wx, -2.5, wz, 1, 1, 1, C.BED_2,  chunkGroup);
          vox(wx, -3.5, wz, 1, 1, 1, C.BED_3,  chunkGroup);
        }
      }

      // 2. Pre-calculate Multiple Path Candidates & Select Optimal Contiguous Route BEFORE Terrain Gen!
      const winner = generateExpansionPathCandidates(cx, cz, fromCx, fromCz, dir);

      // 3. Carve Additional Connector Path Tiles on the Adjacent / Previous Map
      winner.connectorOldTiles.forEach(tile => {
        const k = `${tile.x},${tile.z}`;
        if (!pathSet.has(k)) {
          carveTileForPath(tile.x, tile.z, scene);
        }
      });

      // 4. Stitch Waypoints Seamlessly back to Sanctum Entrance (4, 4)
      const parentChunk = this.chunks.get(`${fromCx},${fromCz}`);
      const parentWps = (parentChunk && parentChunk.fullWaypoints) ? parentChunk.fullWaypoints : WAYPOINTS;

      // Contact point on old map is the last tile in winner.connectorOldTiles
      const contactTile = winner.connectorOldTiles[winner.connectorOldTiles.length - 1];
      let contactIdx = -1;
      let minDist = 999;
      parentWps.forEach((wp, idx) => {
        const d = Math.hypot(wp.x - contactTile.x, wp.z - contactTile.z);
        if (d < minDist) {
          minDist = d;
          contactIdx = idx;
        }
      });
      if (contactIdx === -1) contactIdx = 0;

      const chunkPathWaypoints = winner.newChunkPath.map(pt => new THREE.Vector3(pt[0], 0.85, pt[1]));
      // Connector waypoints: from borderOld up to (but excluding) contactTile
      const connectorWaypoints = winner.connectorOldTiles.slice(0, -1).map(pt => new THREE.Vector3(pt.x, 0.85, pt.z));

      const stitchedWaypoints = [
        ...chunkPathWaypoints,
        ...connectorWaypoints,
        ...parentWps.slice(contactIdx)
      ];

      // 5. Check and destroy any intermediate portals along the extended route
      this.checkAndDestroyMidwayPortals(stitchedWaypoints, winner.portal, fromCx, fromCz);

      // 5. Build Cobblestone Path Meshes on the New Chunk
      const pathSetLocal = new Set(winner.newChunkPath.map(p => `${p[0]},${p[1]}`));
      winner.newChunkPath.forEach((pt, idx) => {
        pathSet.add(`${pt[0]},${pt[1]}`);
        heightMap.set(`${pt[0]},${pt[1]}`, 1);
        const col = (idx % 2 === 0) ? C.COB_L : C.COB_D;
        const px = pt[0], pz = pt[1];
        const m1 = vox(px, 0.42, pz, 0.96, 0.85, 0.96, col, chunkGroup);
        const m2 = vox(px, 0.9, pz - 0.47, 1.0, 0.18, 0.12, C.COB_CURB, chunkGroup);
        const m3 = vox(px, 0.9, pz + 0.47, 1.0, 0.18, 0.12, C.COB_CURB, chunkGroup);
        const m4 = vox(px - 0.47, 0.9, pz, 0.12, 0.18, 1.0, C.COB_CURB, chunkGroup);
        const m5 = vox(px + 0.47, 0.9, pz, 0.12, 0.18, 1.0, C.COB_CURB, chunkGroup);
        registerPathMesh(px, pz, m1);
        registerPathMesh(px, pz, m2);
        registerPathMesh(px, pz, m3);
        registerPathMesh(px, pz, m4);
        registerPathMesh(px, pz, m5);
      });

      // 6. Sandstone Terrain with stepped dunes, zero border cliffs, and clear sightline grading
      generateRoughPatchesForChunk(cx, cz);
      createSandRoughnessTextures();
      for (let lx = 0; lx < 16; lx++) {
        for (let lz = 0; lz < 16; lz++) {
          const wx = originX + lx;
          const wz = originZ + lz;
          if (pathSetLocal.has(`${wx},${wz}`)) continue;

          let h = 1;
          // Smooth lower-frequency noise to produce concentrated, cohesive mesa formations
          const noise = Math.sin(wx * 0.16) * Math.cos(wz * 0.16) + Math.sin((wx + wz) * 0.10);
          if (noise > 1.25) h = 3;
          else if (noise > 0.70) h = 2;

          // Border height matching: ensure seamless flat borders between all sectors
          if (lx === 0 || lx === 15 || lz === 0 || lz === 15) {
            h = 1;
          }

          heightMap.set(`${wx},${wz}`, h);
          for (let y = 1; y <= h; y++) {
            const isTop = (y === h);
            let tileMap = null;
            if (isTop) {
              tileMap = getSandDitherTexture(wx, wz);
            }
            const col = getTerrainColor(y, h, wx, wz, !!tileMap);
            const m = vox(wx, y - 0.5, wz, 1, 1, 1, col, chunkGroup, 0, 0, 1, tileMap);
            registerTerrainVoxel(wx, wz, m);
          }
        }
      }

      // 7. Outer Edge Alien Spawn Portal in new chunk
      const portalGroup = buildPortalMesh(winner.portal.x, 0.85, winner.portal.z);
      chunkGroup.add(portalGroup);

      // 8. 6–8 Rune Pedestals alongside the new path with glowing light beacons
      const chunkPedestals = [];
      const usedPedLocal = new Set();
      const tryAddChunkPed = (px, pz) => {
        if (chunkPedestals.length >= 8) return;
        if (px < originX + 1 || px > originX + 14 || pz < originZ + 1 || pz > originZ + 14) return;
        const k = `${px},${pz}`;
        if (pathSet.has(k) || usedPedLocal.has(k)) return;
        usedPedLocal.add(k);

        // Sightline clearance
        const fg1 = `${px + 1},${pz}`;
        const fg2 = `${px},${pz + 1}`;
        const fg3 = `${px + 1},${pz + 1}`;
        if ((heightMap.get(fg1) || 1) > 1) heightMap.set(fg1, 1);
        if ((heightMap.get(fg2) || 1) > 1) heightMap.set(fg2, 1);
        if ((heightMap.get(fg3) || 1) > 1) heightMap.set(fg3, 1);

        const pedId = this.nextPedestalId++;
        const h = heightMap.get(k) || 1;
        const pedObj = createPedestalMesh(pedId, px, h, pz);
        pedestals.push(pedObj);
        chunkPedestals.push(pedObj);
        chunkGroup.add(pedObj.group);
      };

      winner.chicanes.forEach(c => {
        tryAddChunkPed(c.x + 2, c.z);
        tryAddChunkPed(c.x - 2, c.z);
        tryAddChunkPed(c.x, c.z + 2);
        tryAddChunkPed(c.x, c.z - 2);
      });

      for (let i = 2; i < winner.newChunkPath.length - 2; i += 3) {
        const [px, pz] = winner.newChunkPath[i];
        tryAddChunkPed(px + 2, pz);
        tryAddChunkPed(px - 2, pz);
        tryAddChunkPed(px, pz + 2);
        tryAddChunkPed(px, pz - 2);
        if (chunkPedestals.length >= 7) break;
      }

      // 9. Procedural Decorations for the new sector
      buildProceduralDecorations(chunkGroup, cx, cz, winner.portal);

      // 9b. Procedural Overworld Pebbles for the new sector (Clustered gravel beds, scattered stones)
      populateChunkPebbles(chunkGroup, cx, cz);

      // 10. Prepare Voxel Rise Wave Animation
      const connCenter = winner.borderNew;
      chunkGroup.traverse(child => {
        if (child.isMesh && child.visible && child.material !== child.parent?.userData?.colliderMat) {
          const finalY = child.position.y;
          child.userData.targetY = finalY;
          child.position.y = finalY - 14.0; // submerge below sands

          const dist = Math.hypot(child.position.x - connCenter.x, child.position.z - connCenter.z);
          child.userData.riseDelay = dist * 0.045;
          child.userData.rising = true;
          this.animatingVoxels.push(child);
        }
      });

      scene.add(chunkGroup);

      return {
        cx, cz,
        id: `${cx},${cz}`,
        group: chunkGroup,
        portalPos: new THREE.Vector3(winner.portal.x, 0.85, winner.portal.z),
        portalGroup: portalGroup,
        waypoints: chunkPathWaypoints,
        fullWaypoints: stitchedWaypoints,
        pedestals: chunkPedestals
      };
    },

    updateAnimatingVoxels: function (dt) {
      if (this.animatingVoxels.length === 0) return;

      for (let i = this.animatingVoxels.length - 1; i >= 0; i--) {
        const mesh = this.animatingVoxels[i];
        if (mesh.userData.riseDelay > 0) {
          mesh.userData.riseDelay -= dt;
        } else {
          // Smooth rise upward with easing
          mesh.position.y = THREE.MathUtils.lerp(mesh.position.y, mesh.userData.targetY, dt * 7.0);

          if (Math.abs(mesh.position.y - mesh.userData.targetY) < 0.05) {
            mesh.position.y = mesh.userData.targetY;
            mesh.userData.rising = false;
            this.animatingVoxels.splice(i, 1);

            // Spawn sand particle burst at landing
            if (Math.random() < 0.2) {
              CombatManager.spawnParticleBurst(
                mesh.position.clone().add(new THREE.Vector3(0, 0.4, 0)),
                3,
                C.SAND_L
              );
            }
          }
        }
      }
    },

    createVoxelWedgeArrowMesh: function (dir, exp) {
      const group = new THREE.Group();

      // Tier 1: Dark Foundation Plinth (stepped triangular wedge base flush with slab)
      vox(0, 0.05, -0.9,  2.8, 0.12, 0.6, C.BED_1, group);
      vox(0, 0.05, -0.3,  2.2, 0.12, 0.6, C.BED_1, group);
      vox(0, 0.05,  0.3,  1.6, 0.12, 0.6, C.BED_1, group);
      vox(0, 0.05,  0.85, 1.0, 0.12, 0.5, C.BED_1, group);
      vox(0, 0.05,  1.3,  0.5, 0.12, 0.4, C.BED_1, group);

      // Tier 2: Warm Carved Sandstone Triangular Wedge Slices
      vox(0, 0.18, -0.9,  2.5, 0.16, 0.55, C.SAND_D, group);
      vox(0, 0.18, -0.35, 1.9, 0.16, 0.55, C.SAND_M, group);
      vox(0, 0.18,  0.2,  1.3, 0.16, 0.55, C.SAND_L, group);
      vox(0, 0.18,  0.75, 0.8, 0.16, 0.45, C.SAND_L, group);
      vox(0, 0.18,  1.2,  0.38, 0.16, 0.35, C.SAND_L, group);

      // Tier 3: Stepped Side Terraces & Bevels (Ancient Carved Relief)
      vox(-1.1, 0.28, -0.85, 0.24, 0.10, 0.45, C.PED_BASE, group);
      vox( 1.1, 0.28, -0.85, 0.24, 0.10, 0.45, C.PED_BASE, group);
      vox(-0.8, 0.28, -0.35, 0.24, 0.10, 0.45, C.PED_BASE, group);
      vox( 0.8, 0.28, -0.35, 0.24, 0.10, 0.45, C.PED_BASE, group);
      vox(-0.5, 0.28,  0.15, 0.24, 0.10, 0.45, C.PED_BASE, group);
      vox( 0.5, 0.28,  0.15, 0.24, 0.10, 0.45, C.PED_BASE, group);

      // Tier 4: Carved Stone Ridge Spine
      vox(0, 0.30, -0.1, 0.32, 0.14, 1.8, C.STN_M, group);

      // Rune Meshes to pulse in animation
      const runeMeshes = [];

      // Glowing Gold Runes (Inlaid along the spine and chevrons)
      const r1 = vox(0, 0.38, -0.5, 0.18, 0.08, 0.6, 0xFFD700, group, 0xFFD700, 2.2);
      const r2 = vox(0, 0.38,  0.2, 0.18, 0.08, 0.6, 0xFFD700, group, 0xFFD700, 2.2);
      const rWingL = vox(-0.4, 0.34, -0.2, 0.12, 0.06, 0.35, 0xFFD700, group, 0xFFD700, 2.0);
      const rWingR = vox( 0.4, 0.34, -0.2, 0.12, 0.06, 0.35, 0xFFD700, group, 0xFFD700, 2.0);
      runeMeshes.push(r1, r2, rWingL, rWingR);

      // Glowing Emerald Center Rune Core
      const coreGem = vox(0, 0.40, -0.1, 0.32, 0.12, 0.32, 0x39FF14, group, 0x39FF14, 2.8);
      runeMeshes.push(coreGem);

      // Glowing Forward Arrow Tip Pointer (Cyan crystal prism)
      const tipGem = vox(0, 0.34, 1.25, 0.28, 0.20, 0.35, 0x00E5FF, group, 0x00E5FF, 3.5);
      runeMeshes.push(tipGem);

      // Invisible Box Collider for Raycasting Hover & Click
      const colGeo = new THREE.BoxGeometry(3.2, 1.4, 3.2);
      const colMat = new THREE.MeshBasicMaterial({ visible: false });
      const colMesh = new THREE.Mesh(colGeo, colMat);
      colMesh.position.set(0, 0.3, 0.2);
      colMesh.userData.isArrow = true;
      colMesh.userData.arrowGroup = group;
      colMesh.userData.expansion = exp;
      group.add(colMesh);

      group.userData.collider = colMesh;
      group.userData.runeMeshes = runeMeshes;
      group.userData.expansion = exp;
      group.userData.currentScale = 1.0;
      group.userData.targetScale = 1.0;
      group.userData.emissiveMultiplier = 1.0;

      // Apply direction rotation & outward directional vector
      if (dir === 'south') {
        group.rotation.y = 0;
        group.userData.outwardDir = new THREE.Vector3(0, 0, 1);
      } else if (dir === 'north') {
        group.rotation.y = Math.PI;
        group.userData.outwardDir = new THREE.Vector3(0, 0, -1);
      } else if (dir === 'east') {
        group.rotation.y = Math.PI * 0.5;
        group.userData.outwardDir = new THREE.Vector3(1, 0, 0);
      } else if (dir === 'west') {
        group.rotation.y = -Math.PI * 0.5;
        group.userData.outwardDir = new THREE.Vector3(-1, 0, 0);
      }

      return group;
    },

    spawn3DArrows: function (available) {
      this.clear3DArrows();

      available.forEach(exp => {
        const arrow = this.createVoxelWedgeArrowMesh(exp.dir, exp);
        let ax = 0, az = 0;
        const ay = 1.0; // Flush with upper surface elevation of map slab

        if (exp.dir === 'north') {
          ax = exp.fromCx * 16 + 7.5;
          az = exp.fromCz * 16 - 1.2;
        } else if (exp.dir === 'south') {
          ax = exp.fromCx * 16 + 7.5;
          az = exp.fromCz * 16 + 16.2;
        } else if (exp.dir === 'east') {
          ax = exp.fromCx * 16 + 16.2;
          az = exp.fromCz * 16 + 7.5;
        } else {
          ax = exp.fromCx * 16 - 1.2;
          az = exp.fromCz * 16 + 7.5;
        }

        arrow.position.set(ax, ay, az);
        arrow.userData.basePos = new THREE.Vector3(ax, ay, az);

        this.arrowObjects.push(arrow);
        scene.add(arrow);
      });
    },

    clear3DArrows: function () {
      this.arrowObjects.forEach(arrow => {
        if (arrow.parent) arrow.parent.remove(arrow);
      });
      this.arrowObjects = [];
      if (typeof canvas !== 'undefined' && canvas) {
        canvas.style.cursor = 'default';
      }
    },

    // Legacy Banner Aliases for backwards compatibility
    spawn3DBanners: function (available) { this.spawn3DArrows(available); },
    clear3DBanners: function () { this.clear3DArrows(); },
    animate3DBanners: function (t) { this.animate3DArrows(t, 0.016); },

    animate3DArrows: function (t, dt) {
      const step = dt || 0.016;
      this.arrowObjects.forEach((arrow, idx) => {
        // 1. Scale lerp towards targetScale (smooth 1.25x hover scale)
        const curScale = arrow.userData.currentScale || 1.0;
        const tgtScale = arrow.userData.targetScale || 1.0;
        const newScale = curScale + (tgtScale - curScale) * Math.min(1.0, step * 14.0);
        arrow.userData.currentScale = newScale;
        arrow.scale.set(newScale, newScale, newScale);

        // 2. Smooth outward directional bobbing along outwardDir
        const phase = t * 3.5 + idx * 0.9;
        const outwardBob = Math.sin(phase) * 0.35;
        const vertBob = Math.sin(phase * 1.2) * 0.08;

        const basePos = arrow.userData.basePos;
        if (basePos && arrow.userData.outwardDir) {
          arrow.position.copy(basePos).addScaledVector(arrow.userData.outwardDir, outwardBob);
          arrow.position.y = basePos.y + vertBob;
        }

        // 3. Emissive glow pulse on rune meshes
        const emMult = arrow.userData.emissiveMultiplier || 1.0;
        const basePulse = 1.8 + Math.sin(phase * 1.5) * 0.9;
        if (arrow.userData.runeMeshes) {
          arrow.userData.runeMeshes.forEach(mesh => {
            if (mesh && mesh.material) {
              mesh.material.emissiveIntensity = basePulse * emMult;
            }
          });
        }
      });
    },

    frameCameraForExpansion: function () {
      let minX = Infinity, maxX = -Infinity;
      let minZ = Infinity, maxZ = -Infinity;

      this.chunks.forEach(chunk => {
        minX = Math.min(minX, chunk.cx * 16);
        maxX = Math.max(maxX, chunk.cx * 16 + 16);
        minZ = Math.min(minZ, chunk.cz * 16);
        maxZ = Math.max(maxZ, chunk.cz * 16 + 16);
      });

      this.arrowObjects.forEach(arrow => {
        if (arrow.userData.basePos) {
          minX = Math.min(minX, arrow.userData.basePos.x - 3);
          maxX = Math.max(maxX, arrow.userData.basePos.x + 3);
          minZ = Math.min(minZ, arrow.userData.basePos.z - 3);
          maxZ = Math.max(maxZ, arrow.userData.basePos.z + 3);
        }
      });

      if (!isFinite(minX)) {
        minX = -3; maxX = 19; minZ = -3; maxZ = 19;
      }

      const midX = (minX + maxX) * 0.5;
      const midZ = (minZ + maxZ) * 0.5;
      const spanX = maxX - minX;
      const spanZ = maxZ - minZ;
      const maxSpan = Math.max(spanX, spanZ);

      // In orthographic isometric view, span of 22-24 fits comfortably at zoom ~14.5
      const fitZoom = Math.max(14.0, maxSpan * 0.62);

      targetCameraPos.set(midX, 1.5, midZ);
      targetZoom = fitZoom;
    }
  };

  // ========================================================
  // STRUCTURED 10-WAVE MANAGER (Multi-Portal Weighted Distribution)
  // ========================================================
  const WaveManager = {
    spawnQueue: [],
    spawnTimer: 0,
    portalIndex: 0,
    portalWeights: [],
    portalSpawnCounts: [],
    currentSquadPortal: 0,
    squadRemaining: 0,

    initWavePortalDistribution: function () {
      const portals = (ChunkManager.activePortals && ChunkManager.activePortals.length > 0)
        ? ChunkManager.activePortals
        : [{ waypoints: WAYPOINTS }];

      const n = portals.length;
      if (n === 1) {
        this.portalWeights = [1.0];
      } else if (n === 2) {
        // Dynamic weighted ratio between 0.40/0.60 and 0.60/0.40
        const r = 0.40 + Math.random() * 0.20;
        this.portalWeights = [r, 1.0 - r];
      } else {
        // 3+ portals: guarantee each at least 0.20, dynamic normalized distribution
        const raw = portals.map(() => 0.22 + Math.random() * 0.36);
        const sum = raw.reduce((a, b) => a + b, 0);
        this.portalWeights = raw.map(w => w / sum);
      }

      this.portalSpawnCounts = portals.map(() => 0);
      this.currentSquadPortal = this.pickWeightedPortalIndex();
      this.squadRemaining = 2 + Math.floor(Math.random() * 3); // 2 to 4 enemies in squad burst
    },

    pickWeightedPortalIndex: function () {
      const rand = Math.random();
      let cum = 0;
      for (let i = 0; i < this.portalWeights.length; i++) {
        cum += this.portalWeights[i];
        if (rand <= cum || i === this.portalWeights.length - 1) {
          return i;
        }
      }
      return 0;
    },

    getNextPortalRoute: function (isBoss = false) {
      const portals = (ChunkManager.activePortals && ChunkManager.activePortals.length > 0)
        ? ChunkManager.activePortals
        : [{ waypoints: WAYPOINTS }];

      if (portals.length === 1) return portals[0].waypoints || WAYPOINTS;

      if (!this.portalWeights || this.portalWeights.length !== portals.length) {
        this.initWavePortalDistribution();
      }

      // Bosses pick the least spawned active portal
      if (isBoss) {
        let minIdx = 0;
        let minVal = Infinity;
        for (let i = 0; i < this.portalSpawnCounts.length; i++) {
          if (this.portalSpawnCounts[i] < minVal) {
            minVal = this.portalSpawnCounts[i];
            minIdx = i;
          }
        }
        this.portalSpawnCounts[minIdx]++;
        return portals[minIdx].waypoints || WAYPOINTS;
      }

      // Squad burst: roll next portal if current squad burst finished
      if (this.squadRemaining <= 0) {
        let nextIdx = this.pickWeightedPortalIndex();
        if (portals.length > 1 && nextIdx === this.currentSquadPortal && Math.random() < 0.65) {
          nextIdx = (nextIdx + 1) % portals.length;
        }
        this.currentSquadPortal = nextIdx;
        this.squadRemaining = 2 + Math.floor(Math.random() * 3);
      }

      this.squadRemaining--;
      const pIdx = this.currentSquadPortal % portals.length;
      this.portalSpawnCounts[pIdx] = (this.portalSpawnCounts[pIdx] || 0) + 1;
      return portals[pIdx].waypoints || WAYPOINTS;
    },

    getWaveComposition: function (waveNum) {
      // 1.15^(wave - 1) HP scaling formula for late waves
      const hpScale = Math.pow(1.15, Math.max(0, waveNum - 1));
      const queue = [];

      switch (waveNum) {
        case 1:
          // Wave 1: 7 Scouts (Introductory pacing)
          for (let i = 0; i < 7; i++) queue.push({ type: 'scout', delay: 1.3, hpScale: 1.0 });
          break;
        case 2:
          // Wave 2: 5 Scouts & 5 Troopers
          for (let i = 0; i < 5; i++) queue.push({ type: 'scout', delay: 1.0, hpScale: 1.0 });
          for (let i = 0; i < 5; i++) queue.push({ type: 'trooper', delay: 1.2, hpScale: 1.0 });
          break;
        case 3:
          // Wave 3: Swarm Skitterer packs (0.25s burst) + Troopers
          for (let i = 0; i < 6; i++) queue.push({ type: 'skitterer', delay: 0.25, hpScale: 1.0 });
          for (let i = 0; i < 4; i++) queue.push({ type: 'trooper', delay: 1.1, hpScale: 1.0 });
          for (let i = 0; i < 6; i++) queue.push({ type: 'skitterer', delay: 0.25, hpScale: 1.0 });
          break;
        case 4:
          // Wave 4: Phase Shielders + Troopers + Scouts
          for (let i = 0; i < 4; i++) queue.push({ type: 'shielder', delay: 1.2, hpScale: 1.0 });
          for (let i = 0; i < 5; i++) queue.push({ type: 'trooper', delay: 1.0, hpScale: 1.0 });
          for (let i = 0; i < 4; i++) queue.push({ type: 'scout', delay: 0.9, hpScale: 1.0 });
          break;
        case 5:
          // Wave 5 (Mini-Boss): Troopers & Shielders led by Astral Harvester Boss
          queue.push({ type: 'boss', delay: 1.5, hpScale: 0.55 }); // ~990 HP Mini-Boss
          for (let i = 0; i < 4; i++) queue.push({ type: 'shielder', delay: 1.0, hpScale: 1.0 });
          for (let i = 0; i < 5; i++) queue.push({ type: 'trooper', delay: 0.9, hpScale: 1.0 });
          break;
        case 6:
          // Wave 6: Fast assault
          for (let i = 0; i < 8; i++) queue.push({ type: 'skitterer', delay: 0.25, hpScale: hpScale });
          for (let i = 0; i < 5; i++) queue.push({ type: 'shielder', delay: 0.9, hpScale: hpScale });
          for (let i = 0; i < 8; i++) queue.push({ type: 'skitterer', delay: 0.25, hpScale: hpScale });
          break;
        case 7:
          // Wave 7: Armored column
          for (let i = 0; i < 7; i++) queue.push({ type: 'shielder', delay: 0.9, hpScale: hpScale });
          for (let i = 0; i < 8; i++) queue.push({ type: 'trooper', delay: 0.8, hpScale: hpScale });
          for (let i = 0; i < 6; i++) queue.push({ type: 'scout', delay: 0.7, hpScale: hpScale });
          break;
        case 8:
          // Wave 8: Swarm onslaught
          for (let i = 0; i < 12; i++) queue.push({ type: 'skitterer', delay: 0.22, hpScale: hpScale });
          for (let i = 0; i < 6; i++) queue.push({ type: 'shielder', delay: 0.9, hpScale: hpScale });
          for (let i = 0; i < 6; i++) queue.push({ type: 'trooper', delay: 0.8, hpScale: hpScale });
          break;
        case 9:
          // Wave 9: Elite vanguard
          for (let i = 0; i < 8; i++) queue.push({ type: 'shielder', delay: 0.85, hpScale: hpScale });
          for (let i = 0; i < 8; i++) queue.push({ type: 'trooper', delay: 0.75, hpScale: hpScale });
          for (let i = 0; i < 8; i++) queue.push({ type: 'scout', delay: 0.65, hpScale: hpScale });
          break;
        case 10:
          // Wave 10 (Final Boss): Massive invasion ending with Astral Harvester Boss!
          for (let i = 0; i < 6; i++) queue.push({ type: 'shielder', delay: 0.8, hpScale: 1.0 });
          for (let i = 0; i < 10; i++) queue.push({ type: 'skitterer', delay: 0.25, hpScale: 1.0 });
          for (let i = 0; i < 6; i++) queue.push({ type: 'trooper', delay: 0.8, hpScale: 1.0 });
          queue.push({ type: 'boss', delay: 1.8, hpScale: 1.0 }); // 2200 HP Boss
          break;
        default:
          if (waveNum > 10) {
            // Procedural Endless Mode (Waves 11+)
            const extraWaves = waveNum - 10;
            const totalUnits = 20 + extraWaves * 5;
            const hpScale = Math.pow(1.19, waveNum - 1);
            const delay = Math.max(0.20, 0.75 - extraWaves * 0.035);
            const types = ['skitterer', 'trooper', 'shielder', 'scout'];

            for (let i = 0; i < totalUnits; i++) {
              const type = types[i % types.length];
              queue.push({ type, delay, hpScale });
            }

            // Every 5th wave (15, 20, 25...), spawn Astral Harvester Bosses!
            // Wave 15 spawns 2 bosses (user requested); wave 20+ scales up to 3
            if (waveNum % 5 === 0) {
              const bossCount = (waveNum === 15) ? 2 : Math.min(3, Math.floor((waveNum - 10) / 10) + 1);
              // Controlled boss HP multiplier
              const bossHpMult = Math.min(5.5, 1.2 + (waveNum - 10) * 0.38);
              for (let b = 0; b < bossCount; b++) {
                queue.push({ type: 'boss', delay: 3.0, hpScale: bossHpMult });
              }
            }
          } else {
            for (let i = 0; i < 6; i++) queue.push({ type: 'trooper', delay: 1.0, hpScale: 1.0 });
          }
      }

      return queue;
    },

    startWave: function (waveNum) {
      this.initWavePortalDistribution();
      this.spawnQueue = this.getWaveComposition(waveNum);
      this.spawnTimer = 0.5; // initial pause before first alien emerges
    },

    update: function (dt) {
      if (!GameState.waveActive) return;

      if (this.spawnQueue.length > 0) {
        this.spawnTimer -= dt;
        if (this.spawnTimer <= 0) {
          const item = this.spawnQueue.shift();
          const route = this.getNextPortalRoute(item.type === 'boss');
          new EnemyInstance(item.type, item.hpScale, route);
          this.spawnTimer = item.delay;
        }
      } else {
        this.checkWaveCompletion();
      }
    },

    checkWaveCompletion: function () {
      if (GameState.waveActive && this.spawnQueue.length === 0 && activeEnemies.length === 0) {
        GameState.onWaveComplete();
      }
    }
  };

  // ========================================================
  // HUD & UI BINDINGS (Pixel-Voxel HUD)
  // ========================================================

  function updateHud() {
    // 1. Sanctum Vitality
    const hpText = document.getElementById('hud-hp-text');
    if (hpText) hpText.textContent = `${GameState.sanctumHp} / ${GameState.maxSanctumHp}`;
    const hpBar = document.getElementById('hud-hp-bar');
    if (hpBar) {
      const pct = Math.max(0, Math.min(100, (GameState.sanctumHp / GameState.maxSanctumHp) * 100));
      hpBar.style.width = `${pct}%`;
    }

    // 2. Ancient Shards
    const shardsEl = document.getElementById('hud-shards');
    if (shardsEl) shardsEl.textContent = `${GameState.shards}`;

    // 2b. Astral Essence
    const essenceEl = document.getElementById('hud-essence');
    if (essenceEl) essenceEl.textContent = `${GameState.essence}`;

    // 3. Wave Tracker
    const waveEl = document.getElementById('hud-wave');
    if (waveEl) {
      if (GameState.endlessMode || GameState.currentWave > 10) {
        waveEl.textContent = `WAVE ${GameState.currentWave} (ENDLESS)`;
      } else {
        waveEl.textContent = `WAVE ${GameState.currentWave} / ${GameState.totalWaves}`;
      }
    }

    // 4. Wave Start Action Button
    const waveBtn = document.getElementById('btn-wave');
    if (waveBtn) {
      if (GameState.awaitingExpansion) {
        waveBtn.disabled = false;
        waveBtn.textContent = '🗺️ CHOOSE AN EDGE';
        waveBtn.classList.add('pulse-gold');
      } else if (GameState.waveActive) {
        waveBtn.disabled = true;
        waveBtn.textContent = 'WAVE IN PROGRESS...';
        waveBtn.classList.remove('pulse-gold');
      } else if (GameState.gameOver) {
        waveBtn.disabled = true;
        waveBtn.textContent = 'SANCTUM BREACHED';
        waveBtn.classList.remove('pulse-gold');
      } else if (GameState.currentWave >= GameState.totalWaves && !GameState.endlessMode) {
        waveBtn.disabled = true;
        waveBtn.textContent = '🏆 VICTORY!';
        waveBtn.classList.remove('pulse-gold');
      } else {
        waveBtn.disabled = false;
        const nextWaveNum = GameState.currentWave + 1;
        waveBtn.textContent = `▶ START WAVE ${nextWaveNum} [SPACE]`;
        waveBtn.classList.add('pulse-gold');
      }
    }

    // 5. Speed Button (1x -> 2x -> 4x -> 1x)
    const btnSpeed = document.getElementById('btn-speed');
    if (btnSpeed) {
      btnSpeed.textContent = (GameState.gameSpeed === 4.0) ? `🔥 ${GameState.gameSpeed}x` : `⚡ ${GameState.gameSpeed}x`;
      btnSpeed.classList.toggle('active-speed', GameState.gameSpeed >= 2.0);
      btnSpeed.classList.toggle('super-speed', GameState.gameSpeed === 4.0);
    }

    // 6. Golem Dock Cards Affordability & Active Highlight
    document.querySelectorAll('.golem-card').forEach(card => {
      const type = card.getAttribute('data-type');
      const cfg = GOLEM_CONFIGS[type];
      card.classList.toggle('active', type === GameState.selectedGolemType);
      if (cfg) {
        card.classList.toggle('disabled', GameState.shards < cfg.cost);
      }
    });

    // 7. Contextual Inspector Update
    if (GameState.selectedGolem) {
      openGolemInspector(GameState.selectedGolem);
    }
  }

  // Crisp Front-Facing Blocky Voxel Golem Portraits (Pixel-Art SVGs)
  const GOLEM_PORTRAITS = {
    stone: `
      <svg viewBox="0 0 36 36" width="100%" height="100%" style="shape-rendering: crispEdges; display: block;">
        <rect x="0" y="0" width="36" height="36" fill="#14100E"/>
        <rect x="4" y="24" width="28" height="12" fill="#585B5F"/>
        <rect x="2" y="27" width="32" height="9" fill="#3A3C3E"/>
        <rect x="6" y="23" width="6" height="3" fill="#A4A8AB"/>
        <rect x="24" y="23" width="6" height="3" fill="#A4A8AB"/>
        <rect x="8" y="7" width="20" height="17" fill="#7A7E82"/>
        <rect x="10" y="5" width="16" height="3" fill="#A4A8AB"/>
        <rect x="9" y="11" width="18" height="3" fill="#585B5F"/>
        <rect x="11" y="14" width="4" height="2" fill="#00E5FF"/>
        <rect x="21" y="14" width="4" height="2" fill="#00E5FF"/>
        <rect x="9" y="8" width="3" height="3" fill="#4E8A32"/>
        <rect x="24" y="18" width="3" height="3" fill="#4E8A32"/>
        <rect x="12" y="18" width="12" height="5" fill="#585B5F"/>
        <rect x="14" y="20" width="8" height="2" fill="#3A3C3E"/>
      </svg>
    `,
    oak: `
      <svg viewBox="0 0 36 36" width="100%" height="100%" style="shape-rendering: crispEdges; display: block;">
        <rect x="0" y="0" width="36" height="36" fill="#14100E"/>
        <rect x="14" y="2" width="8" height="4" fill="#2E7D32"/>
        <rect x="11" y="5" width="14" height="3" fill="#4CAF50"/>
        <rect x="4" y="24" width="28" height="12" fill="#54300F"/>
        <rect x="2" y="27" width="32" height="9" fill="#3E2723"/>
        <rect x="7" y="24" width="4" height="4" fill="#4A4D50"/>
        <rect x="25" y="24" width="4" height="4" fill="#4A4D50"/>
        <rect x="9" y="8" width="18" height="16" fill="#7E4C1D"/>
        <rect x="11" y="9" width="14" height="4" fill="#DEBD8C"/>
        <rect x="10" y="14" width="16" height="3" fill="#3E2723"/>
        <rect x="12" y="14" width="4" height="2" fill="#39FF14"/>
        <rect x="20" y="14" width="4" height="2" fill="#39FF14"/>
        <rect x="13" y="19" width="10" height="4" fill="#54300F"/>
        <rect x="15" y="20" width="6" height="2" fill="#DEBD8C"/>
      </svg>
    `,
    brick: `
      <svg viewBox="0 0 36 36" width="100%" height="100%" style="shape-rendering: crispEdges; display: block;">
        <rect x="0" y="0" width="36" height="36" fill="#14100E"/>
        <rect x="12" y="3" width="12" height="4" fill="#2A3335"/>
        <rect x="14" y="1" width="8" height="3" fill="#1A2122"/>
        <rect x="3" y="23" width="30" height="13" fill="#803320"/>
        <rect x="1" y="26" width="34" height="10" fill="#5A2416"/>
        <rect x="8" y="7" width="20" height="17" fill="#A84A32"/>
        <rect x="8" y="11" width="20" height="1" fill="#803320"/>
        <rect x="8" y="16" width="20" height="1" fill="#803320"/>
        <rect x="14" y="7" width="1" height="4" fill="#803320"/>
        <rect x="21" y="7" width="1" height="4" fill="#803320"/>
        <rect x="17" y="12" width="1" height="4" fill="#803320"/>
        <rect x="11" y="13" width="4" height="2" fill="#FFD700"/>
        <rect x="21" y="13" width="4" height="2" fill="#FFD700"/>
        <rect x="12" y="19" width="12" height="5" fill="#2A3335"/>
        <rect x="14" y="20" width="2" height="3" fill="#FF6D00"/>
        <rect x="17" y="20" width="2" height="3" fill="#FF6D00"/>
        <rect x="20" y="20" width="2" height="3" fill="#FF6D00"/>
      </svg>
    `,
    diorite: `
      <svg viewBox="0 0 36 36" width="100%" height="100%" style="shape-rendering: crispEdges; display: block;">
        <rect x="0" y="0" width="36" height="36" fill="#14100E"/>
        <rect x="16" y="2" width="4" height="4" fill="#E040FB"/>
        <rect x="14" y="4" width="8" height="2" fill="#BA68C8"/>
        <rect x="4" y="24" width="28" height="12" fill="#D0D7DE"/>
        <rect x="2" y="27" width="32" height="9" fill="#283236"/>
        <rect x="9" y="8" width="18" height="16" fill="#F6F8FA"/>
        <rect x="7" y="12" width="2" height="8" fill="#8B949E"/>
        <rect x="27" y="12" width="2" height="8" fill="#8B949E"/>
        <rect x="11" y="9" width="14" height="3" fill="#E1E4E8"/>
        <rect x="11" y="14" width="4" height="2" fill="#00E5FF"/>
        <rect x="21" y="14" width="4" height="2" fill="#00E5FF"/>
        <rect x="16" y="18" width="4" height="4" fill="#00E5FF"/>
        <rect x="13" y="19" width="10" height="2" fill="#8B949E"/>
      </svg>
    `
  };

  function openGolemInspector(golem) {
    const insp = document.getElementById('golem-inspector');
    if (!insp || !golem) return;

    // 1. Header & Badge
    const nameEl = document.getElementById('insp-name');
    if (nameEl) nameEl.textContent = golem.config.name;

    // 1b. Golem Attack Style & Damage Type Badge
    const typeBadge = document.getElementById('insp-type-badge');
    if (typeBadge) {
      const attackStyles = {
        stone: 'AoE Splash',
        oak: 'Single Target (Fast)',
        brick: '360° Seismic Slam',
        diorite: 'Multi-Target Beam'
      };
      const elemLabels = {
        thunder: '⚡ Thunder',
        earth: '🌍 Earth',
        fire: '🔥 Fire',
        water: '💧 Water'
      };
      const baseDmgTypes = {
        diorite: 'Magic',
        stone: 'Physical',
        oak: 'Physical',
        brick: 'Physical'
      };
      const currentDmg = golem.element ? elemLabels[golem.element] : baseDmgTypes[golem.type];
      typeBadge.textContent = `${attackStyles[golem.type] || 'Combat'} · ${currentDmg}`;
    }

    const lvlBadge = document.getElementById('insp-level');
    if (lvlBadge) {
      if (golem.level >= 5) {
        lvlBadge.textContent = 'LV. 5 MAX';
        lvlBadge.title = `👑 PRIMAL ASCENDANCE: ${golem.config.ascendDesc}`;
      } else if (golem.level >= 3) {
        lvlBadge.textContent = `LV. ${golem.level} ★`;
        lvlBadge.title = `⭐ TIER 3 CAPSTONE: ${golem.config.capstoneDesc}`;
      } else {
        lvlBadge.textContent = `LV. ${golem.level}`;
        lvlBadge.title = `Golem Level ${golem.level}`;
      }
      lvlBadge.className = `pixel-badge lvl-${golem.level}`;
    }

    const starEl = document.getElementById('insp-capstone-star');
    if (starEl) {
      starEl.classList.toggle('hidden', golem.level < 3);
      if (golem.level >= 3) {
        starEl.title = `⭐ TIER 3 CAPSTONE: ${golem.config.capstoneDesc}`;
      }
    }

    // 2. Compact Stats Readout (DMG, RNG, SPD) & Damage Type Tag
    const dmgEl = document.getElementById('insp-dmg');
    const rngEl = document.getElementById('insp-range');
    const apsEl = document.getElementById('insp-aps');
    const dmgTypeTag = document.getElementById('insp-dmg-type');

    if (dmgEl) dmgEl.textContent = `${golem.damage}`;
    if (rngEl) rngEl.textContent = `${golem.range}`;
    if (apsEl) apsEl.textContent = `${(1 / golem.cooldown).toFixed(2)}`;
    if (dmgTypeTag) {
      if (golem.element) {
        dmgTypeTag.textContent = golem.element.toUpperCase();
      } else {
        dmgTypeTag.textContent = (golem.type === 'diorite') ? 'MAGIC' : 'PHYS';
      }
    }

    // 3. Voxel Portrait & Elemental Socket Orb (o)
    const portraitBox = document.getElementById('insp-portrait');
    if (portraitBox && GOLEM_PORTRAITS[golem.type]) {
      portraitBox.innerHTML = GOLEM_PORTRAITS[golem.type];
    }

    const orbEl = document.getElementById('insp-elem-orb');
    if (orbEl) {
      orbEl.className = 'elem-orb-socket';
      const iconMap = { thunder: '⚡', earth: '🌍', fire: '🔥', water: '💧' };
      const nameMap = {
        thunder: '⚡ Thunder (+Zapped Stun)',
        earth: '🌍 Earth (+30% Dmg, Knockback, 30% Slow)',
        fire: '🔥 Fire (+50% Dmg, Burned 2% HP/s, Combustion)',
        water: '💧 Water (+AoE Splash, Wet 2x Thunder, Combustion)'
      };
      if (golem.element && iconMap[golem.element]) {
        orbEl.classList.add(`elem-${golem.element}`);
        orbEl.innerHTML = `<span class="orb-icon">${iconMap[golem.element]}</span>`;
        orbEl.title = `${nameMap[golem.element]} [Active Infusion]`;
      } else {
        orbEl.innerHTML = `<span class="orb-icon">·</span>`;
        orbEl.title = 'Elemental Socket: Uninfused (Click Element to infuse 1 🔮)';
      }
    }

    // 4. Ascend Ability Preview Banner
    const ascendBanner = document.getElementById('insp-ascend-banner');
    const ascendStatus = document.getElementById('ascend-status-label');
    const ascendDesc = document.getElementById('ascend-desc-text');
    if (ascendBanner && ascendStatus && ascendDesc) {
      const simpleAscendPerks = {
        stone: 'Mega Meteor (3.2-tile crater shockwave + magma)',
        oak: 'Twin Ballista (Attacks 2 targets with kinetic spikes)',
        brick: 'Cataclysmic Quake (3.6-tile radius, 0.9s stun & shred)',
        diorite: 'Supernova Conduit (Chains 6 targets & deep 50% slow)'
      };
      ascendDesc.textContent = simpleAscendPerks[golem.type] || golem.config.ascendDesc;
      if (golem.level >= 5) {
        ascendStatus.textContent = '👑 ASCENDED:';
        ascendBanner.classList.add('active-ascended');
      } else {
        ascendStatus.textContent = 'LV.5 ASCEND:';
        ascendBanner.classList.remove('active-ascended');
      }
    }

    // 5. Middle Action Row: [ Upgrade ] & [ Element ] (Stacked 2-line layout)
    const upBtn = document.getElementById('btn-upgrade');
    const upAction = document.getElementById('upgrade-btn-action');
    const upCost = document.getElementById('upgrade-btn-cost');
    if (upBtn) {
      if (golem.level >= 5) {
        if (upAction) upAction.textContent = 'MAX LEVEL';
        if (upCost) upCost.textContent = '👑 ASCENDED';
        upBtn.classList.add('max-level');
        upBtn.disabled = true;
      } else {
        const upgradeCost = golem.getUpgradeCost();
        if (upAction) upAction.textContent = (golem.level === 4) ? 'ASCEND' : 'UPGRADE';
        if (upCost) upCost.textContent = `${upgradeCost} 💎`;
        upBtn.classList.remove('max-level');
        upBtn.disabled = (GameState.shards < upgradeCost);
      }
    }

    const elemBtn = document.getElementById('btn-element-toggle');
    const elemAction = document.getElementById('element-btn-action');
    const elemCost = document.getElementById('element-btn-cost');
    if (elemBtn) {
      elemBtn.className = 'pixel-btn action-btn element-toggle-btn';
      if (golem.element) {
        elemBtn.classList.add(`infused-${golem.element}`);
        const iconMap = { thunder: '⚡', earth: '🌍', fire: '🔥', water: '💧' };
        if (elemAction) elemAction.textContent = `${iconMap[golem.element] || '🔮'} ${golem.element.toUpperCase()}`;
        if (elemCost) elemCost.textContent = 'INFUSED';
      } else {
        if (elemAction) elemAction.textContent = '🔮 ELEMENT';
        if (elemCost) elemCost.textContent = '1 🔮';
      }
    }

    // 6. Elemental Popover Options Active Highlighting
    document.querySelectorAll('.element-option-btn').forEach(btn => {
      const elem = btn.getAttribute('data-element');
      btn.classList.toggle('active', golem.element === elem);
      btn.disabled = (GameState.essence < 1 && golem.element !== elem);
    });

    // 7. 4-Grid Priority Selector Highlighting
    updateTargetingButtons(golem.targetingMode);

    // 8. Bottom-Right Sell Button
    const sellBtn = document.getElementById('btn-sell');
    if (sellBtn) {
      const sellRefund = Math.round(golem.totalInvested * 0.70);
      sellBtn.textContent = `SELL (+${sellRefund}💎)`;
    }

    // Hide any floating popovers when switching golem
    const popover = document.getElementById('element-popover');
    if (popover) popover.classList.add('hidden');

    insp.classList.remove('hidden');
  }

  function closeGolemInspector() {
    const insp = document.getElementById('golem-inspector');
    if (insp) insp.classList.add('hidden');
    const popover = document.getElementById('element-popover');
    if (popover) popover.classList.add('hidden');
    // Hide any hovering preview deltas
    ['delta-dmg', 'delta-range', 'delta-aps'].forEach(id => {
      const el = document.getElementById(id);
      if (el) el.classList.add('hidden');
    });
  }

  function updateTargetingButtons(activeMode) {
    const tagEl = document.getElementById('priority-active-tag');
    const pLabels = { first: 'FIRST', last: 'LAST', strongest: 'STRONG', closest: 'CLOSE' };
    if (tagEl) tagEl.textContent = pLabels[activeMode] || 'FIRST';

    document.querySelectorAll('.priority-4grid .target-btn').forEach(btn => {
      btn.classList.toggle('active', btn.getAttribute('data-mode') === activeMode);
    });
  }

  // ========================================================
  // CLEAN GAME RESET
  // ========================================================

  function resetGame() {
    if (GameState.defeatInterval) {
      clearInterval(GameState.defeatInterval);
      GameState.defeatInterval = null;
    }

    // 1. Remove all active enemies
    for (let i = activeEnemies.length - 1; i >= 0; i--) {
      const e = activeEnemies[i];
      if (e.model && e.model.parent) e.model.parent.remove(e.model);
      if (e.healthBarGroup && e.healthBarGroup.parent) e.healthBarGroup.parent.remove(e.healthBarGroup);
    }
    activeEnemies = [];

    // 2. Remove all active projectiles
    for (let i = activeProjectiles.length - 1; i >= 0; i--) {
      const p = activeProjectiles[i];
      if (p.mesh && p.mesh.parent) p.mesh.parent.remove(p.mesh);
    }
    activeProjectiles = [];

    // 3. Remove all particles, beams & slam rings
    for (let i = activeParticles.length - 1; i >= 0; i--) {
      const p = activeParticles[i];
      if (p.mesh && p.mesh.parent) p.mesh.parent.remove(p.mesh);
    }
    activeParticles = [];

    for (let i = activeBeams.length - 1; i >= 0; i--) {
      const b = activeBeams[i];
      if (b.mesh && b.mesh.parent) b.mesh.parent.remove(b.mesh);
    }
    activeBeams = [];

    for (let i = activeSlamRings.length - 1; i >= 0; i--) {
      const s = activeSlamRings[i];
      if (s.mesh && s.mesh.parent) s.mesh.parent.remove(s.mesh);
    }
    activeSlamRings = [];

    // Clear active tornadoes
    for (let i = activeTornadoes.length - 1; i >= 0; i--) {
      const t = activeTornadoes[i];
      if (t.mesh && t.mesh.parent) t.mesh.parent.remove(t.mesh);
    }
    activeTornadoes = [];

    // 4. Clear floating text & golem inspector
    FloatingTextManager.clear();
    closeGolemInspector();

    // 5. Remove placed Golems and clear pedestals
    for (let i = activeGolems.length - 1; i >= 0; i--) {
      const g = activeGolems[i];
      if (g.model && g.model.parent) g.model.parent.remove(g.model);
      if (g.pedestal) g.pedestal.golem = null;
    }
    activeGolems = [];

    // 6. Tear down previous map & procedurally generate brand new level!
    destroyCurrentLevel();
    buildProceduralStartingIsland();

    // 7. Reset GameState
    GameState.shards = 150;
    GameState.essence = 0;
    GameState.sanctumHp = 20;
    GameState.maxSanctumHp = 20;
    GameState.currentWave = 0;
    GameState.totalWaves = 10;
    GameState.waveActive = false;
    GameState.gameOver = false;
    GameState.gameWon = false;
    GameState.endlessMode = false;
    GameState.realmExpanded = false;
    GameState.totalKills = 0;
    GameState.totalShardsEarned = 150;
    GameState.deselect();

    // 8. Reset WaveManager queue & ChunkManager
    WaveManager.spawnQueue = [];
    WaveManager.spawnTimer = 0;
    ChunkManager.init();

    // 9. Reset camera position, target & zoom
    cameraTarget.set(7.5, 1.5, 7.5);
    targetCameraPos.set(7.5, 1.5, 7.5);
    cameraZoom = 10.5;
    targetZoom = 10.5;
    updateCamera();

    // 10. Reset defeat button text, modals & boss bar
    const btnDefReset = document.getElementById('btn-defeat-reset');
    if (btnDefReset) btnDefReset.textContent = '⚔️ TRY AGAIN (NEW REALM)';

    const modVic = document.getElementById('modal-victory');
    const modDef = document.getElementById('modal-gameover');
    const bossBar = document.getElementById('boss-bar-container');
    if (modVic) modVic.classList.add('hidden');
    if (modDef) modDef.classList.add('hidden');
    if (bossBar) bossBar.classList.add('hidden');

    FloatingTextManager.spawnText(
      new THREE.Vector3(7.5, 3.5, 7.5),
      '🌌 NEW REALM MANIFESTED!',
      'shard-reward'
    );

    updateHud();
  }

  // ========================================================
  // 3D STAGE SELECTION CAROUSEL MANAGER (Title Screen)
  // ========================================================

  const STAGES_CONFIG = [
    {
      id: 'desert',
      title: 'STAGE I: SUNSCORCHED OASIS',
      name: 'Sunscorched Oasis',
      badge: 'UNLOCKED · ACTIVE REALM',
      isUnlocked: true,
      desc: 'Sun-drenched sandstone mesa protected by the First Monolith. Sunken turquoise oasis springs with winding cobblestone paths.'
    },
    {
      id: 'frost',
      title: 'STAGE II: FROSTFANG REACHES',
      name: 'Frostfang Reaches',
      badge: 'LOCKED · REACH WAVE 20',
      isUnlocked: false,
      desc: 'A blizzard-swept tundra of perpetual permafrost. High-density alien skitterers burrow deep beneath the ice sheets.'
    },
    {
      id: 'volcanic',
      title: 'STAGE III: VOLCANIC CALDERA',
      name: 'Volcanic Caldera',
      badge: 'LOCKED · REACH WAVE 30',
      isUnlocked: false,
      desc: 'Hazardous tectonic rift with bubbling magma fissures. Heavy alien shock columns with fire immunity emerge here.'
    },
    {
      id: 'verdant',
      title: 'STAGE IV: CANOPY GROVE',
      name: 'Canopy Grove',
      badge: 'LOCKED · REACH WAVE 40',
      isUnlocked: false,
      desc: 'Dense alien flora with spore clouds and poisonous thickets surrounding the overgrown sanctum monolith.'
    },
    {
      id: 'astral',
      title: 'STAGE V: ASTRAL VOID SPIRES',
      name: 'Astral Spires',
      badge: 'LOCKED · REACH WAVE 50',
      isUnlocked: false,
      desc: 'Floating ruins suspended in the deep cosmic void. Lair of the twin Astral Leviathan dreadnoughts.'
    }
  ];

  const StageCarouselManager = {
    renderer: null,
    scene: null,
    camera: null,
    canvas: null,
    stageGroups: [],
    currentIndex: 0,
    initialized: false,

    init: function () {
      this.canvas = document.getElementById('stage-carousel-canvas');
      if (!this.canvas) return;

      try {
        this.renderer = new THREE.WebGLRenderer({
          canvas: this.canvas,
          alpha: true,
          antialias: true,
          powerPreference: 'default'
        });
        this.renderer.setSize(600, 340, false);
        this.renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
        this.renderer.shadowMap.enabled = true;
        this.renderer.shadowMap.type = THREE.PCFSoftShadowMap;

        this.scene = new THREE.Scene();
        this.camera = new THREE.PerspectiveCamera(36, 600 / 340, 0.1, 100);
        this.camera.position.set(0, 5.8, 12.5);
        this.camera.lookAt(0, 0.4, 0);

        // Lighting
        const amb = new THREE.AmbientLight(0xFFFFFF, 0.85);
        this.scene.add(amb);
        const sun = new THREE.DirectionalLight(0xFFE8C2, 1.35);
        sun.position.set(6, 12, 8);
        sun.castShadow = true;
        this.scene.add(sun);
        const rim = new THREE.DirectionalLight(0x4080FF, 0.5);
        rim.position.set(-6, 3, -6);
        this.scene.add(rim);

        // Build 5 3D Stage Diorama Groups
        this.stageGroups = [];
        for (let i = 0; i < STAGES_CONFIG.length; i++) {
          let grp;
          if (i === 0) {
            grp = this.buildDesertDiorama();
          } else {
            grp = this.buildLockedGreyDiorama(i);
          }
          this.scene.add(grp);
          this.stageGroups.push(grp);
        }

        this.setupEventListeners();
        this.updateUI();
        this.initialized = true;
      } catch (err) {
        console.warn('StageCarouselManager init failed:', err);
      }
    },

    buildDesertDiorama: function () {
      const g = new THREE.Group();
      g.userData.isUnlocked = true;

      const cVox = (x, y, z, w, h, d, col, parent, emCol, emInt, op) => {
        const mat = new THREE.MeshLambertMaterial({
          color: col,
          emissive: emCol || 0x000000,
          emissiveIntensity: emInt || 0,
          transparent: (op !== undefined && op < 1),
          opacity: op !== undefined ? op : 1.0
        });
        const m = new THREE.Mesh(new THREE.BoxGeometry(w, h, d), mat);
        m.position.set(x, y, z);
        m.castShadow = true;
        m.receiveShadow = true;
        (parent || g).add(m);
        return m;
      };

      // 1. Stepped Voxel Island Base
      cVox(0, -0.65, 0, 3.8, 0.5, 3.8, 0x5C3E14);
      cVox(0, -0.25, 0, 4.4, 0.4, 4.4, 0x8C6020);
      cVox(0, 0.15, 0, 4.8, 0.45, 4.8, 0xDF9E34);

      // Elevated mesa backdrop in North-West
      cVox(-1.2, 0.55, -1.2, 2.2, 0.4, 2.2, 0xCF8424);
      cVox(-1.5, 0.90, -1.5, 1.4, 0.35, 1.4, 0xE5A63D);

      // 2. Sunken Turquoise Oasis Lagoon
      const water = cVox(1.2, 0.18, 1.1, 1.8, 0.06, 1.6, 0x00B0FF, g, 0x00B0FF, 0.6, 0.85);
      g.userData.water = water;
      // Damp sand rim
      cVox(1.2, 0.22, 1.95, 1.9, 0.08, 0.16, 0xC68A2E);
      cVox(1.2, 0.22, 0.25, 1.9, 0.08, 0.16, 0xC68A2E);
      cVox(0.25, 0.22, 1.1, 0.16, 0.08, 1.7, 0xC68A2E);
      cVox(2.15, 0.22, 1.1, 0.16, 0.08, 1.7, 0xC68A2E);
      // Lily pads
      cVox(0.9, 0.22, 0.8, 0.35, 0.03, 0.3, 0x2E7D32);
      cVox(1.6, 0.22, 1.4, 0.3, 0.03, 0.26, 0x43A047);

      // 3. Palm Tree on dry sand beside oasis
      const trunk = new THREE.Group();
      trunk.position.set(1.6, 0.35, 0.0);
      cVox(0, 0.3, 0, 0.18, 0.6, 0.18, 0x5D4037, trunk);
      cVox(0.06, 0.8, 0, 0.16, 0.5, 0.16, 0x6D4C41, trunk);
      cVox(0.14, 1.25, 0, 0.14, 0.45, 0.14, 0x795548, trunk);
      // Canopy fronds
      cVox(0.14, 1.5, 0, 0.8, 0.12, 0.8, 0x2E7D32, trunk);
      cVox(0.14, 1.6, 0, 0.5, 0.12, 0.5, 0x43A047, trunk);
      cVox(-0.35, 1.38, 0, 0.4, 0.08, 0.25, 0x388E3C, trunk);
      cVox( 0.65, 1.38, 0, 0.4, 0.08, 0.25, 0x388E3C, trunk);
      g.add(trunk);

      // 4. Cobblestone Path winding from edge to Sanctum
      const pathPts = [
        [-1.8, 0.7], [-1.2, 0.7], [-0.6, 0.7], [0.0, 0.4], [0.0, -0.2], [-0.5, -0.7]
      ];
      pathPts.forEach((pt, idx) => {
        const col = (idx % 2 === 0) ? 0x8A8D91 : 0x63666A;
        cVox(pt[0], 0.36, pt[1], 0.55, 0.06, 0.55, col);
      });

      // 5. Miniature Ancient Sanctum Monolith
      const sGroup = new THREE.Group();
      sGroup.position.set(-1.4, 1.1, -1.4);
      cVox(0, 0.08, 0, 1.1, 0.16, 0.9, 0x585B5F, sGroup);
      cVox(-0.38, 0.6, 0, 0.22, 0.9, 0.22, 0x7A7E82, sGroup);
      cVox( 0.38, 0.6, 0, 0.22, 0.9, 0.22, 0x7A7E82, sGroup);
      cVox(0, 1.12, 0, 1.15, 0.18, 0.32, 0x585B5F, sGroup);
      const core = cVox(0, 0.6, 0, 0.28, 0.28, 0.28, 0x39FF14, sGroup, 0x39FF14, 3.0);
      g.userData.core = core;
      g.add(sGroup);

      // 6. Alien Portal on entry path
      const pGroup = new THREE.Group();
      pGroup.position.set(-2.0, 0.35, 0.7);
      cVox(0, 0.4, 0, 0.16, 0.75, 0.55, 0x1A1126, pGroup);
      cVox(0, 0.4, 0, 0.08, 0.65, 0.42, 0xE040FB, pGroup, 0xE040FB, 2.5);
      g.add(pGroup);

      // 7. Golden Aura Ring Beneath Island
      const ringGeo = new THREE.RingGeometry(2.7, 3.4, 36);
      const ringMat = new THREE.MeshBasicMaterial({
        color: 0xFFD700,
        side: THREE.DoubleSide,
        transparent: true,
        opacity: 0.8
      });
      const ring = new THREE.Mesh(ringGeo, ringMat);
      ring.rotation.x = -Math.PI / 2;
      ring.position.y = -0.92;
      g.add(ring);
      g.userData.auraRing = ring;

      return g;
    },

    buildLockedGreyDiorama: function (stageIdx) {
      const g = new THREE.Group();
      g.userData.isUnlocked = false;

      const cVox = (x, y, z, w, h, d, col, parent) => {
        const mat = new THREE.MeshLambertMaterial({ color: col });
        const m = new THREE.Mesh(new THREE.BoxGeometry(w, h, d), mat);
        m.position.set(x, y, z);
        m.castShadow = true;
        m.receiveShadow = true;
        (parent || g).add(m);
        return m;
      };

      const baseGrey = (stageIdx === 1) ? 0x4A4D52 : (stageIdx === 2 ? 0x3A3A3C : (stageIdx === 3 ? 0x404842 : 0x2E2C33));
      const midGrey  = (stageIdx === 1) ? 0x5D6168 : (stageIdx === 2 ? 0x4D4D50 : (stageIdx === 3 ? 0x525C54 : 0x3E3A45));
      const topGrey  = (stageIdx === 1) ? 0x767B82 : (stageIdx === 2 ? 0x626266 : (stageIdx === 3 ? 0x67736A : 0x514C5A));

      // Stepped floating island silhouette in pure stone grey tones (NO assets, NO trees, NO oasis)
      cVox(0, -0.65, 0, 3.8, 0.5, 3.8, baseGrey);
      cVox(0, -0.25, 0, 4.4, 0.4, 4.4, midGrey);
      cVox(0,  0.15, 0, 4.8, 0.45, 4.8, topGrey);

      // Raw craggy stone ridges on surface
      cVox(-1.2, 0.45, -1.0, 2.0, 0.3, 2.0, midGrey);
      cVox( 1.1, 0.40,  0.9, 1.8, 0.25, 1.6, midGrey);
      cVox(-0.3, 0.42,  1.3, 1.2, 0.22, 1.4, baseGrey);

      // Floating Glowing 3D Voxel Question Mark "?"
      const qGroup = new THREE.Group();
      qGroup.position.set(0, 1.15, 0);

      const qMat = new THREE.MeshLambertMaterial({
        color: 0xFFD700,
        emissive: 0xFFD700,
        emissiveIntensity: 2.2
      });
      const qBox = (x, y, z, w, h, d) => {
        const m = new THREE.Mesh(new THREE.BoxGeometry(w, h, d), qMat);
        m.position.set(x, y, z);
        qGroup.add(m);
        return m;
      };

      qBox(0, 0.15, 0, 0.32, 0.32, 0.32);     // Dot
      qBox(0, 0.75, 0, 0.30, 0.52, 0.30);     // Lower stem
      qBox(0.26, 1.18, 0, 0.32, 0.45, 0.30);   // Right curve
      qBox(0.05, 1.52, 0, 0.72, 0.32, 0.30);   // Top bar
      qBox(-0.25, 1.30, 0, 0.30, 0.35, 0.30);  // Left drop

      g.add(qGroup);
      g.userData.questionMark = qGroup;

      // Subtle muted grey ring
      const ringGeo = new THREE.RingGeometry(2.7, 3.2, 32);
      const ringMat = new THREE.MeshBasicMaterial({
        color: 0x555555,
        side: THREE.DoubleSide,
        transparent: true,
        opacity: 0.35
      });
      const ring = new THREE.Mesh(ringGeo, ringMat);
      ring.rotation.x = -Math.PI / 2;
      ring.position.y = -0.92;
      g.add(ring);
      g.userData.auraRing = ring;

      return g;
    },

    setupEventListeners: function () {
      const btnPrev = document.getElementById('btn-stage-prev');
      const btnNext = document.getElementById('btn-stage-next');
      if (btnPrev) {
        btnPrev.addEventListener('click', () => {
          this.cycleStage(-1);
        });
      }
      if (btnNext) {
        btnNext.addEventListener('click', () => {
          this.cycleStage(1);
        });
      }

      // Pagination dots
      const dots = document.querySelectorAll('.stage-dot');
      dots.forEach(dot => {
        dot.addEventListener('click', e => {
          const idx = parseInt(e.target.getAttribute('data-index'), 10);
          if (!isNaN(idx)) this.selectStage(idx);
        });
      });

      // Guide Modal Navigation Tabs
      document.querySelectorAll('.guide-nav-tab').forEach(tab => {
        tab.addEventListener('click', e => {
          document.querySelectorAll('.guide-nav-tab').forEach(t => t.classList.remove('active'));
          tab.classList.add('active');
          const targetId = tab.getAttribute('data-target');
          const targetEl = document.getElementById(targetId);
          if (targetEl) {
            targetEl.scrollIntoView({ behavior: 'smooth', block: 'start' });
          }
        });
      });
    },

    cycleStage: function (dir) {
      const count = STAGES_CONFIG.length;
      let next = (this.currentIndex + dir + count) % count;
      this.selectStage(next);
      GameState.playSound('stoneImpact');
    },

    selectStage: function (index) {
      this.currentIndex = index;
      this.updateUI();
    },

    updateUI: function () {
      const stage = STAGES_CONFIG[this.currentIndex];
      if (!stage) return;

      const titleEl = document.getElementById('stage-display-title');
      const badgeEl = document.getElementById('stage-display-badge');
      const descEl  = document.getElementById('stage-display-desc');
      const counterEl = document.getElementById('stage-counter-text');

      if (titleEl) titleEl.textContent = stage.title;
      if (badgeEl) {
        badgeEl.textContent = stage.badge;
        badgeEl.className = `stage-display-badge ${stage.isUnlocked ? 'badge-unlocked' : 'badge-locked'}`;
      }
      if (descEl) descEl.textContent = stage.desc;
      if (counterEl) counterEl.textContent = `STAGE ${this.currentIndex + 1} / ${STAGES_CONFIG.length}`;

      // Update dots
      document.querySelectorAll('.stage-dot').forEach((dot, idx) => {
        dot.classList.toggle('active', idx === this.currentIndex);
      });

      // Update Left Panel active status card
      const leftTag = document.getElementById('title-selected-stage-tag');
      const leftName = document.getElementById('title-selected-stage-name');
      if (leftTag) {
        leftTag.textContent = stage.isUnlocked ? 'STAGE I · ACTIVE' : `STAGE ${this.currentIndex + 1} · LOCKED`;
        leftTag.className = `status-tag ${stage.isUnlocked ? 'unlocked' : 'locked'}`;
      }
      if (leftName) {
        leftName.textContent = stage.name;
      }
    },

    update: function (dt, t) {
      if (!this.initialized || !this.renderer) return;

      const count = STAGES_CONFIG.length;
      for (let i = 0; i < count; i++) {
        const grp = this.stageGroups[i];
        if (!grp) continue;

        let diff = i - this.currentIndex;
        if (diff > Math.floor(count / 2)) diff -= count;
        if (diff < -Math.floor(count / 2)) diff += count;

        let targetPos, targetScale, targetRotY;

        if (diff === 0) {
          // Center / Selected Stage
          const hoverY = Math.sin(t * 1.8) * 0.12;
          targetPos = new THREE.Vector3(0, hoverY, 0);
          targetScale = 0.88;
          targetRotY = t * 0.32;
          grp.visible = true;

          // Pulse glowing aura ring underneath
          if (grp.userData.auraRing) {
            grp.userData.auraRing.rotation.z += 0.8 * dt;
            grp.userData.auraRing.material.opacity = 0.75 + Math.sin(t * 3.0) * 0.2;
          }
        } else if (diff === -1) {
          // Left adjacent stage (smaller, tilted)
          const hoverY = -0.22 + Math.sin(t * 1.8 + 1.2) * 0.08;
          targetPos = new THREE.Vector3(-5.0, hoverY, -2.2);
          targetScale = 0.52;
          targetRotY = t * 0.20 + 0.35;
          grp.visible = true;
          if (grp.userData.auraRing) grp.userData.auraRing.material.opacity = 0.25;
        } else if (diff === 1) {
          // Right adjacent stage (smaller, tilted)
          const hoverY = -0.22 + Math.sin(t * 1.8 + 2.4) * 0.08;
          targetPos = new THREE.Vector3(5.0, hoverY, -2.2);
          targetScale = 0.52;
          targetRotY = t * 0.20 - 0.35;
          grp.visible = true;
          if (grp.userData.auraRing) grp.userData.auraRing.material.opacity = 0.25;
        } else {
          // Far stages
          targetPos = new THREE.Vector3((diff > 0 ? 8.5 : -8.5), -1.0, -5.0);
          targetScale = 0.20;
          targetRotY = 0;
          grp.visible = false;
        }

        // Smooth Lerp
        grp.position.lerp(targetPos, 0.14);
        const curScale = grp.scale.x;
        const newScale = THREE.MathUtils.lerp(curScale, targetScale, 0.14);
        grp.scale.set(newScale, newScale, newScale);
        grp.rotation.y = THREE.MathUtils.lerp(grp.rotation.y, targetRotY, 0.18);

        // Animate question mark on locked stages
        if (grp.userData.questionMark) {
          grp.userData.questionMark.rotation.y += 1.8 * dt;
          grp.userData.questionMark.position.y = 1.15 + Math.sin(t * 2.8 + i) * 0.10;
        }

        // Animate sanctum core on desert stage
        if (grp.userData.core) {
          grp.userData.core.rotation.y += 2.2 * dt;
          grp.userData.core.rotation.x += 1.2 * dt;
        }
      }

      this.renderer.render(this.scene, this.camera);
    }
  };

  // ========================================================
  // INPUT CONTROLS & RAYCASTING (Pointer Isolation)
  // ========================================================

  function setupControls() {
    const canvas = renderer.domElement;
    let dragging = false;
    let prevX = 0, prevY = 0;
    let totalDragDist = 0;

    const camRight = new THREE.Vector3(1, 0, -1).normalize();
    const camUp    = new THREE.Vector3(-1, 0, -1).normalize();

    // Prevent Raycaster Bleed-Through: Stop propagation on all HUD containers & modals
    const uiContainers = [
      '#title-screen',
      '#top-bar',
      '#boss-bar-container',
      '#golem-inspector',
      '#golem-dock',
      '#modal-victory',
      '#modal-gameover',
      '#modal-expansion',
      '#modal-settings',
      '#modal-guide'
    ];
    uiContainers.forEach(sel => {
      const el = document.querySelector(sel);
      if (el) {
        ['pointerdown', 'mousedown', 'mouseup', 'click'].forEach(evt => {
          el.addEventListener(evt, e => e.stopPropagation());
        });
      }
    });

    // Lazy initialization of Web Audio context on first user interaction
    ['pointerdown', 'mousedown', 'keydown'].forEach(evt => {
      window.addEventListener(evt, () => SoundManager.resumeContext(), { once: true });
    });

    // Mouse Down on canvas
    canvas.addEventListener('mousedown', e => {
      dragging = true;
      prevX = e.clientX;
      prevY = e.clientY;
      totalDragDist = 0;
    });

    // Mouse Move (Pan & Pedestal Hover)
    window.addEventListener('mousemove', e => {
      if (dragging) {
        const dx = e.clientX - prevX;
        const dy = e.clientY - prevY;
        prevX = e.clientX;
        prevY = e.clientY;
        totalDragDist += Math.abs(dx) + Math.abs(dy);

        const speed = cameraZoom * 0.0028;
        targetCameraPos.add(camRight.clone().multiplyScalar(-dx * speed));
        targetCameraPos.add(camUp.clone().multiplyScalar(dy * speed));
      } else {
        // Pedestal & 3D Voxel Arrow Raycasting on Hover
        const rect = canvas.getBoundingClientRect();
        mouse.x = ((e.clientX - rect.left) / rect.width) * 2 - 1;
        mouse.y = -((e.clientY - rect.top) / rect.height) * 2 + 1;

        raycaster.setFromCamera(mouse, camera);
        const colliders = pedestals.map(p => p.collider);
        const arrowColliders = ChunkManager.arrowObjects.map(b => b.userData.collider).filter(Boolean);
        const intersects = raycaster.intersectObjects([...arrowColliders, ...colliders]);

        let hitArrow = null;
        if (intersects.length > 0) {
          const hitObj = intersects[0].object;
          if (hitObj.userData.isArrow) {
            hitArrow = hitObj.userData.arrowGroup;
          } else if (hitObj.userData.pedestal) {
            const ped = hitObj.userData.pedestal;
            if (hoveredPedestal !== ped) {
              hoveredPedestal = ped;
              updateRangeRingPreview();
            }
          }
        }

        // Arrow hover scaling (1.25x) and bright emissive feedback
        ChunkManager.arrowObjects.forEach(arrow => {
          if (arrow === hitArrow) {
            arrow.userData.targetScale = 1.25;
            arrow.userData.emissiveMultiplier = 2.0;
          } else {
            arrow.userData.targetScale = 1.0;
            arrow.userData.emissiveMultiplier = 1.0;
          }
        });

        if (hitArrow) {
          canvas.style.cursor = 'pointer';
          if (hoveredPedestal !== null) {
            hoveredPedestal = null;
            updateRangeRingPreview();
          }
        } else if (hoveredPedestal) {
          canvas.style.cursor = 'pointer';
        } else {
          canvas.style.cursor = 'default';
          if (hoveredPedestal !== null) {
            hoveredPedestal = null;
            updateRangeRingPreview();
          }
        }
      }
    });

    // Mouse Up on canvas (Summon / Select / Deselect / 3D Arrow Expansion)
    window.addEventListener('mouseup', e => {
      if (!dragging) return;
      dragging = false;

      // If clicked without dragging, test selection or 3D arrow expansion
      if (totalDragDist < 6) {
        const rect = canvas.getBoundingClientRect();
        mouse.x = ((e.clientX - rect.left) / rect.width) * 2 - 1;
        mouse.y = -((e.clientY - rect.top) / rect.height) * 2 + 1;

        raycaster.setFromCamera(mouse, camera);
        const arrowColliders = ChunkManager.arrowObjects.map(b => b.userData.collider).filter(Boolean);
        const colliders = pedestals.map(p => p.collider);
        const intersects = raycaster.intersectObjects([...arrowColliders, ...colliders]);

        if (intersects.length > 0) {
          const hitObj = intersects[0].object;
          if (hitObj.userData.isArrow) {
            const exp = hitObj.userData.expansion;
            ChunkManager.selectExpansion(exp);
            return;
          }

          const ped = hitObj.userData.pedestal;
          if (ped) {
            if (ped.golem) {
              // Select existing Golem
              GameState.selectPedestal(ped);
            } else {
              // Summon Golem on empty pedestal
              summonGolem(ped, GameState.selectedGolemType);
            }
          }
        } else {
          // Clicked empty terrain: deselect and hide inspector
          GameState.deselect();
        }
      }
    });

    // Zoom (Wheel)
    canvas.addEventListener('wheel', e => {
      e.preventDefault();
      targetZoom += e.deltaY * 0.008;
      targetZoom = Math.max(4.0, Math.min(16.0, targetZoom));
    }, { passive: false });

    // Keyboard Shortcuts
    window.addEventListener('keydown', e => {
      if (e.key === '1') GameState.selectGolemType('stone');
      else if (e.key === '2') GameState.selectGolemType('oak');
      else if (e.key === '3') GameState.selectGolemType('brick');
      else if (e.key === '4') GameState.selectGolemType('diorite');
      else if (e.key === ' ' || e.code === 'Space') {
        e.preventDefault();
        GameState.startNextWave();
      } else if (e.key === 'r' || e.key === 'R') {
        targetCameraPos.set(7.5, 1.5, 7.5);
        targetZoom = 10.5;
      } else if (e.key === 'Escape') {
        GameState.deselect();
      }
    });

    // Top Command Bar Buttons
    const btnWave = document.getElementById('btn-wave');
    if (btnWave) btnWave.addEventListener('click', () => GameState.startNextWave());

    const btnSpeed = document.getElementById('btn-speed');
    if (btnSpeed) btnSpeed.addEventListener('click', () => GameState.toggleSpeed());

    const btnAudio = document.getElementById('btn-audio');
    if (btnAudio) btnAudio.addEventListener('click', () => SoundManager.toggleMute());

    // Settings HUD button
    const btnSettingsHud = document.getElementById('btn-settings-hud');
    if (btnSettingsHud) {
      btnSettingsHud.addEventListener('click', () => {
        document.getElementById('modal-settings')?.classList.remove('hidden');
      });
    }

    // Title Screen Menu Buttons
    const btnPlay = document.getElementById('btn-play');
    if (btnPlay) {
      btnPlay.addEventListener('click', () => {
        if (typeof StageCarouselManager !== 'undefined' && StageCarouselManager.currentIndex !== 0) {
          // If locked stage was selected, auto-select Desert Sanctum (Stage I) and proceed
          StageCarouselManager.selectStage(0);
        }
        const titleScreen = document.getElementById('title-screen');
        if (titleScreen) {
          titleScreen.classList.add('fading-out');
          setTimeout(() => titleScreen.classList.add('hidden'), 400);
        }
        GameState.inTitleScreen = false;
        targetCameraPos.set(7.5, 1.5, 7.5);
        targetZoom = 10.5;
        SoundManager.resumeContext();
        GameState.playSound('expansionUnlock');
      });
    }

    const btnTitleSettings = document.getElementById('btn-title-settings');
    if (btnTitleSettings) {
      btnTitleSettings.addEventListener('click', () => {
        document.getElementById('modal-settings')?.classList.remove('hidden');
      });
    }

    const btnTitleGuide = document.getElementById('btn-title-guide');
    if (btnTitleGuide) {
      btnTitleGuide.addEventListener('click', () => {
        document.getElementById('modal-guide')?.classList.remove('hidden');
      });
    }

    // Modal Close Buttons
    const btnCloseSettings = document.getElementById('btn-close-settings');
    if (btnCloseSettings) {
      btnCloseSettings.addEventListener('click', () => {
        document.getElementById('modal-settings')?.classList.add('hidden');
      });
    }

    const btnCloseGuide = document.getElementById('btn-close-guide');
    if (btnCloseGuide) {
      btnCloseGuide.addEventListener('click', () => {
        document.getElementById('modal-guide')?.classList.add('hidden');
      });
    }

    // Settings Controls
    const sliderMaster = document.getElementById('slider-master-vol');
    if (sliderMaster) {
      sliderMaster.addEventListener('input', e => {
        SoundManager.setMasterVolume(parseFloat(e.target.value) / 100);
      });
    }

    const sliderSfx = document.getElementById('slider-sfx-vol');
    if (sliderSfx) {
      sliderSfx.addEventListener('input', e => {
        SoundManager.setSfxVolume(parseFloat(e.target.value) / 100);
      });
    }

    const btnMuteSettings = document.getElementById('btn-toggle-mute-settings');
    if (btnMuteSettings) {
      btnMuteSettings.addEventListener('click', () => {
        SoundManager.toggleMute();
      });
    }

    const chkVignette = document.getElementById('chk-vignette');
    if (chkVignette) {
      chkVignette.addEventListener('change', e => {
        GameState.vignetteEnabled = e.target.checked;
      });
    }

    const btnResetCam = document.getElementById('btn-reset-cam-settings');
    if (btnResetCam) {
      btnResetCam.addEventListener('click', () => {
        targetCameraPos.set(7.5, 1.5, 7.5);
        targetZoom = 10.5;
      });
    }

    // Realm Expansion Button in Victory Modal
    const btnExpandRealm = document.getElementById('btn-expand-realm');
    if (btnExpandRealm) {
      btnExpandRealm.addEventListener('click', () => {
        document.getElementById('modal-victory')?.classList.add('hidden');
        ChunkManager.showExpansionPrompt();
      });
    }

    // Inspector Buttons & Stop Propagation Guards
    const inspPanel = document.getElementById('golem-inspector');
    if (inspPanel) {
      ['pointerdown', 'mousedown', 'mouseup', 'click'].forEach(evt => {
        inspPanel.addEventListener(evt, e => e.stopPropagation());
      });
    }

    const btnCloseInsp = document.getElementById('btn-close-insp');
    if (btnCloseInsp) btnCloseInsp.addEventListener('click', () => GameState.deselect());

    document.querySelectorAll('.golem-card').forEach(card => {
      card.addEventListener('click', () => {
        GameState.selectGolemType(card.getAttribute('data-type'));
      });
    });

    // 4-Grid Priority Targeting Selection
    document.querySelectorAll('.priority-4grid .target-btn').forEach(btn => {
      btn.addEventListener('click', e => {
        e.stopPropagation();
        const golem = GameState.selectedGolem;
        if (!golem) return;
        const mode = btn.getAttribute('data-mode');
        golem.setTargetingMode(mode);
      });
    });

    // Elemental Popover Toggle & Click Outside
    const elemPopover = document.getElementById('element-popover');
    const btnElemToggle = document.getElementById('btn-element-toggle');
    const elemOrbSocket = document.getElementById('insp-elem-orb');

    if (btnElemToggle && elemPopover) {
      btnElemToggle.addEventListener('click', e => {
        e.stopPropagation();
        elemPopover.classList.toggle('hidden');
      });
    }
    if (elemOrbSocket && elemPopover) {
      elemOrbSocket.addEventListener('click', e => {
        e.stopPropagation();
        elemPopover.classList.toggle('hidden');
      });
    }

    document.addEventListener('click', e => {
      if (elemPopover && !elemPopover.classList.contains('hidden')) {
        if (!elemPopover.contains(e.target) && !btnElemToggle?.contains(e.target) && !elemOrbSocket?.contains(e.target)) {
          elemPopover.classList.add('hidden');
        }
      }
    });

    document.querySelectorAll('.element-option-btn').forEach(btn => {
      btn.addEventListener('click', e => {
        e.stopPropagation();
        if (GameState.selectedGolem) {
          const elem = btn.getAttribute('data-element');
          GameState.selectedGolem.applyElement(elem);
          if (elemPopover) elemPopover.classList.add('hidden');
          openGolemInspector(GameState.selectedGolem);
        }
      });
    });

    // Upgrade button with live stat delta preview on hover
    const btnUpgrade = document.getElementById('btn-upgrade');
    if (btnUpgrade) {
      btnUpgrade.addEventListener('mouseenter', () => {
        const golem = GameState.selectedGolem;
        if (!golem || golem.level >= 5) return;

        const dmgMult = (golem.level === 4) ? 1.35 : 1.30;
        const rangeMult = (golem.level === 4) ? 1.10 : 1.08;
        const cdMult = (golem.level === 4) ? 0.85 : 0.88;

        const nextDmg = Math.round(golem.damage * dmgMult);
        const nextRange = +(golem.range * rangeMult).toFixed(2);
        const nextAps = +(1 / (golem.cooldown * cdMult)).toFixed(2);
        const currAps = +(1 / golem.cooldown).toFixed(2);

        const dDmg = document.getElementById('delta-dmg');
        const dRange = document.getElementById('delta-range');
        const dAps = document.getElementById('delta-aps');

        if (dDmg) { dDmg.textContent = `+${nextDmg - golem.damage}`; dDmg.classList.remove('hidden'); }
        if (dRange) { dRange.textContent = `+${(nextRange - golem.range).toFixed(2)}`; dRange.classList.remove('hidden'); }
        if (dAps) { dAps.textContent = `+${(nextAps - currAps).toFixed(2)}`; dAps.classList.remove('hidden'); }
      });

      btnUpgrade.addEventListener('mouseleave', () => {
        ['delta-dmg', 'delta-range', 'delta-aps'].forEach(id => {
          const el = document.getElementById(id);
          if (el) el.classList.add('hidden');
        });
      });

      btnUpgrade.addEventListener('click', () => {
        if (GameState.selectedGolem) GameState.selectedGolem.upgrade();
      });
    }

    const btnSell = document.getElementById('btn-sell');
    if (btnSell) {
      btnSell.addEventListener('click', () => {
        if (GameState.selectedGolem) GameState.selectedGolem.sell();
      });
    }

    // Modal Buttons (Endless Mode & Reset)
    const btnEndless = document.getElementById('btn-endless');
    if (btnEndless) {
      btnEndless.addEventListener('click', () => {
        const modal = document.getElementById('modal-victory');
        if (modal) modal.classList.add('hidden');
        GameState.endlessMode = true;
        GameState.waveActive = false;
        GameState.gameWon = false;
        updateHud();
      });
    }

    const btnVicReset = document.getElementById('btn-victory-reset');
    if (btnVicReset) btnVicReset.addEventListener('click', () => resetGame());

    const btnDefReset = document.getElementById('btn-defeat-reset');
    if (btnDefReset) btnDefReset.addEventListener('click', () => resetGame());
  }

  // ========================================================
  // MAIN ANIMATION LOOP (Strict Time-Step Rule)
  // ========================================================

  function animate() {
    requestAnimationFrame(animate);

    // CRITICAL: Strictly regulated time-step multiplied by gameSpeed
    const rawDt = clock.getDelta();
    const dt = Math.min(rawDt, 0.1) * GameState.gameSpeed;
    const t = clock.getElapsedTime();

    // Camera glide interpolation or Title Screen cinematic orbit
    if (GameState.inTitleScreen) {
      const titleCamAngle = t * 0.12;
      const titleRadius = 42;
      camera.position.x = 7.5 + Math.cos(titleCamAngle) * titleRadius;
      camera.position.z = 7.5 + Math.sin(titleCamAngle) * titleRadius;
      camera.position.y = 7.5 + titleRadius * 0.72;
      camera.lookAt(7.5, 1.5, 7.5);

      // Render 3D Stage Carousel while on Title Screen
      if (typeof StageCarouselManager !== 'undefined' && StageCarouselManager.update) {
        StageCarouselManager.update(rawDt, t);
      }
    } else {
      cameraTarget.lerp(targetCameraPos, 0.08);
      cameraZoom += (targetZoom - cameraZoom) * 0.08;
      updateCamera();
    }

    // Update rising voxels and 3D wedge arrows in ChunkManager
    if (typeof ChunkManager !== 'undefined') {
      ChunkManager.updateAnimatingVoxels(dt);
      ChunkManager.animate3DArrows(t, dt);
    }

    // Update Wave Manager
    WaveManager.update(dt);

    // Update Golems
    for (let i = 0; i < activeGolems.length; i++) {
      activeGolems[i].update(dt);
    }

    // Update Enemies
    for (let i = activeEnemies.length - 1; i >= 0; i--) {
      activeEnemies[i].update(dt);
    }

    // Update Projectiles
    for (let i = activeProjectiles.length - 1; i >= 0; i--) {
      if (activeProjectiles[i].update(dt)) {
        activeProjectiles.splice(i, 1);
      }
    }

    // Update Particles
    for (let i = activeParticles.length - 1; i >= 0; i--) {
      if (activeParticles[i].update(dt)) {
        activeParticles.splice(i, 1);
      }
    }

    // Update Beams
    for (let i = activeBeams.length - 1; i >= 0; i--) {
      if (activeBeams[i].update(dt)) {
        activeBeams.splice(i, 1);
      }
    }

    // Update Slam & Aura Rings
    for (let i = activeSlamRings.length - 1; i >= 0; i--) {
      if (activeSlamRings[i].update(dt)) {
        activeSlamRings.splice(i, 1);
      }
    }

    // Update Voxel Tornadoes
    for (let i = activeTornadoes.length - 1; i >= 0; i--) {
      if (activeTornadoes[i].update(dt)) {
        activeTornadoes.splice(i, 1);
      }
    }

    // Update 2D Floating World-to-Screen Text
    FloatingTextManager.update(dt);

    // Conditional Boss Health Bar Overlay
    const boss = activeEnemies.find(e => e.isBoss && !e.isDead && !e.reachedSanctum);
    const bossBar = document.getElementById('boss-bar-container');
    if (boss && bossBar) {
      bossBar.classList.remove('hidden');
      const pct = Math.max(0, Math.min(100, (boss.hp / boss.maxHp) * 100));
      const fill = document.getElementById('boss-hp-bar');
      const text = document.getElementById('boss-hp-text');
      if (fill) fill.style.width = `${pct}%`;
      if (text) text.textContent = `${Math.max(0, Math.round(boss.hp))} / ${boss.maxHp}`;
    } else if (bossBar && !bossBar.classList.contains('hidden')) {
      bossBar.classList.add('hidden');
    }

    // Waterfall & Oasis ambient animations
    waterfallFlow.forEach((w, i) => {
      w.position.y = w.userData.baseY + Math.sin(t * 5.0 + i * 0.9) * 0.035;
    });
    waterfallFoam.forEach((f, i) => {
      f.position.y = f.userData.baseY + Math.cos(t * 6.5 + i * 1.1) * 0.04;
    });
    oasisWater.forEach((ow, i) => {
      ow.position.y = ow.userData.baseY + Math.sin(t * 1.6 + i * 0.7) * 0.02;
      if (ow.material && ow.material.emissiveIntensity !== undefined) {
        ow.material.emissiveIntensity = 0.3 + Math.sin(t * 2.0 + i) * 0.15;
      }
    });

    // Wind and environmental prop movement animations
    WindManager.update(dt, t);
    const gust = WindManager.gust;
    for (let i = 0; i < environmentalProps.length; i++) {
      const prop = environmentalProps[i];
      if (!prop.parent) continue;
      const dType = prop.userData.decorType;

      if ((dType === 'palm_tree' || dType === 'palm') && prop.userData.crownGroup) {
        const cr = prop.userData.crownGroup;
        cr.rotation.z = Math.sin(t * 1.8 + i * 0.7) * 0.08 * gust;
        cr.rotation.x = Math.cos(t * 1.4 + i * 0.9) * 0.05 * gust;
      } else if ((dType === 'acacia' || dType === 'acacia_tree' || dType === 'flora_cluster') && prop.userData.canopyGroup) {
        const cn = prop.userData.canopyGroup;
        cn.rotation.z = Math.sin(t * 1.3 + i * 0.6) * 0.04 * gust;
        cn.rotation.x = Math.cos(t * 1.1 + i * 0.8) * 0.03 * gust;
      } else if (dType === 'tumbleweed') {
        prop.rotation.y = Math.sin(t * 2.5 + i) * 0.2;
        prop.position.y = prop.userData.baseY + Math.abs(Math.sin(t * 3.2 + i * 1.3)) * 0.035;
      } else if (dType === 'desert_shrub' || dType === 'shrub') {
        prop.rotation.z = Math.sin(t * 2.8 + i * 0.9) * 0.045 * gust;
        prop.rotation.x = Math.cos(t * 2.4 + i * 0.7) * 0.035 * gust;
      } else if (dType && (dType.startsWith('saguaro') || dType === 'saguaro_short' || dType === 'saguaro_norm' || dType === 'saguaro_tall')) {
        prop.rotation.z = Math.sin(t * 1.5 + i * 0.6) * 0.02 * gust;
        prop.rotation.x = Math.cos(t * 1.2 + i * 0.8) * 0.015 * gust;
      } else if (dType === 'prickly_pear' || dType === 'barrel_cactus' || dType === 'barrel') {
        prop.rotation.z = Math.sin(t * 2.2 + i * 0.5) * 0.018 * gust;
      } else if (dType === 'oasis' || dType === 'oasis_feature' || dType === 'grand_oasis') {
        if (prop.userData.reeds) {
          prop.userData.reeds.forEach((rd, rIdx) => {
            rd.rotation.z = Math.sin(t * 2.4 + rIdx * 0.8 + i) * 0.07 * gust;
            rd.rotation.x = Math.cos(t * 2.0 + rIdx * 0.5 + i) * 0.04 * gust;
          });
        }
        if (prop.userData.lilyPads) {
          prop.userData.lilyPads.forEach((lp, lIdx) => {
            lp.position.y = lp.userData.baseY + Math.sin(t * 1.7 + lIdx * 1.2 + i) * 0.02;
            lp.rotation.y = lp.userData.baseRot + Math.sin(t * 0.8 + lIdx + i) * 0.06;
          });
        }
        if (prop.userData.crownGroup) {
          const cr = prop.userData.crownGroup;
          cr.rotation.z = Math.sin(t * 1.8 + i * 0.7) * 0.08 * gust;
          cr.rotation.x = Math.cos(t * 1.4 + i * 0.9) * 0.05 * gust;
        }
      } else if ((dType === 'runic_glyph' || dType === 'ancient_ruins') && prop.userData.runeMeshes) {
        const rGlow = 1.6 + Math.sin(t * 2.6 + i * 0.8) * 0.6;
        prop.userData.runeMeshes.forEach(rm => {
          if (rm.material) rm.material.emissiveIntensity = rGlow;
        });
      }
    }

    // Dynamic wind ambience sound modulation
    SoundManager.updateAmbience(WindManager.gust);

    // Damage vignette & eye flash timers
    if (damageVignetteTimer > 0) {
      damageVignetteTimer -= dt;
      if (damageVignetteTimer <= 0) {
        const vig = document.getElementById('damage-vignette');
        if (vig) vig.classList.remove('hit');
      }
    }

    if (sanctumHitTimer > 0) {
      sanctumHitTimer -= dt;
      if (sanctumHitTimer <= 0 && !GameState.gameOver) {
        sanctumEyes.forEach(eye => {
          eye.material = getMat(C.GLOW_GRN, C.GLOW_GRN, 1.8);
        });
      }
    }

    // Sanctum eye pulse (when not flashing red and game not over)
    if (sanctumHitTimer <= 0 && !GameState.gameOver) {
      const eyeGlow = 1.4 + Math.sin(t * 2.2) * 0.6;
      sanctumEyes.forEach(eye => {
        eye.material.emissiveIntensity = eyeGlow;
      });
    }
    if (sanctumLight) {
      sanctumLight.intensity = 1.0 + Math.sin(t * 2.2) * 0.5;
    }

    // Portal Rune Glow
    const portalGlow = 1.2 + Math.sin(t * 3.0) * 0.4;
    portalRunes.forEach(pr => {
      pr.material.emissiveIntensity = portalGlow;
    });

    // Pedestal Beacon rotation & bobbing (for empty pedestals)
    for (let i = 0; i < pedestals.length; i++) {
      const p = pedestals[i];
      if (!p.golem && p.beaconGroup && p.beaconGroup.visible) {
        if (p.beaconGroup.userData.diamond) {
          p.beaconGroup.userData.diamond.rotation.y += 1.8 * dt;
          p.beaconGroup.userData.diamond.position.y = 3.0 + Math.sin(t * 3.0 + p.id) * 0.08;
        }
      }
    }

    renderer.render(scene, camera);
  }

  // ========================================================
  // RESIZE
  // ========================================================

  function onResize() {
    renderer.setSize(
      Math.floor(window.innerWidth / PIXEL_SCALE),
      Math.floor(window.innerHeight / PIXEL_SCALE),
      false
    );
    updateCamera();
  }

  // ========================================================
  // BOOT
  // ========================================================

  function init() {
    initScene();
    setupLighting();
    buildProceduralStartingIsland();
    ChunkManager.init();
    FloatingTextManager.init();
    StageCarouselManager.init();
    setupControls();
    updateHud();

    window.addEventListener('resize', onResize);
    animate();
  }

  // Expose GameEngine bridge to window for Phase 3 UI & testing
  window.GameEngine = {
    GameState,
    WaveManager,
    CombatManager,
    SoundManager,
    ChunkManager,
    FloatingTextManager,
    StageCarouselManager,
    STAGES_CONFIG,
    GolemInstance,
    EnemyInstance,
    get WAYPOINTS() { return WAYPOINTS; },
    get PATH_TILES() { return PATH_TILES; },
    GOLEM_CONFIGS,
    ALIEN_CONFIGS,
    summonGolem,
    resetGame,
    destroyCurrentLevel,
    buildProceduralStartingIsland,
    get islandRootObjects() { return islandRootObjects; },
    get pedestals() { return pedestals; },
    get activeGolems() { return activeGolems; },
    get activeEnemies() { return activeEnemies; },
    get activeProjectiles() { return activeProjectiles; },
    get activeParticles() { return activeParticles; },
    get activeTornadoes() { return activeTornadoes; },
    get heightMap() { return heightMap; },
    getTerrainHeight: (x, z) => getTerrainHeight(x, z),
    get camera() { return camera; },
    ChunkManager,
    showExpansionPrompt: () => ChunkManager.showExpansionPrompt(),
    selectExpansion: (exp) => ChunkManager.selectExpansion(exp),
    get arrowObjects() { return ChunkManager.arrowObjects; },
    openGolemInspector: (g) => openGolemInspector(g),
    closeGolemInspector: () => closeGolemInspector(),
    setCameraTarget: (x, y, z) => { targetCameraPos.set(x, y, z); cameraTarget.set(x, y, z); updateCamera(); },
    setCameraZoom: (z) => { targetZoom = z; cameraZoom = z; updateCamera(); },
    TerrainAssetLibrary,
    buildProceduralDecorations: (p, cx, cz, ep) => buildProceduralDecorations(p, cx, cz, ep),
    get decorByCell() { return decorByCell; },
    get terrainMeshesByCell() { return terrainMeshesByCell; },
    getTileRoughnessLevel: (wx, wz) => getTileRoughnessLevel(wx, wz),
    getSandDitherTexture: (wx, wz) => getSandDitherTexture(wx, wz),
    getRoughnessScalar: (wx, wz) => getRoughnessScalar(wx, wz),
    populateChunkPebbles: (p, cx, cz) => populateChunkPebbles(p, cx, cz),
    spawnTinyPebble: (p, x, y, z) => spawnTinyPebble(p, x, y, z),
    PEBBLE_COLORS,
    WindManager,
    get environmentalProps() { return environmentalProps; },
    get oasisWater() { return oasisWater; },
    get waterfallFlow() { return waterfallFlow; },
    get waterfallFoam() { return waterfallFoam; },
    get activeRoughPatches() { return activeRoughPatches; },
    generateRoughPatchesForChunk: (cx, cz) => generateRoughPatchesForChunk(cx, cz),
    get scene() { return scene; }
  };

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }

})();
